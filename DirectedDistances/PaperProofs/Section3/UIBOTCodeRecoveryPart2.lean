/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart1
public import DirectedDistances.PaperProofs.Section3.UIBOTPeanoStageIdentification








public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 3.9: a local Peano successor relation on
rotation data. Descent searches the terminal star for its first outgoing dart;
rotation and climb use explicit adjacent darts. This relation makes no claim
that a successor exists for arbitrary rotation data. -/
@[expose] def UIBOTLocalPeanoNext {D : Type*} (rot : Equiv.Perm D)
    (flip : D → D) (tail : D → Prop) (a b : D) : Prop := by
  classical
  exact if tail (rot.symm (flip a)) then
    ∃ k : ℕ, b = (rot ^ k) (flip a) ∧ tail b ∧
      ∀ l : ℕ, l < k → ¬ tail ((rot ^ l) (flip a))
  else if tail (rot a) then b = rot a else b = flip (rot.symm (flip a))

/-- Helper toward Proposition 3.9: the local successor rule is single
valued on arbitrary rotation data. No source, sink, enumeration, or global
injectivity of a coding map is used. -/
theorem uibotLocalPeanoNext_unique {D : Type*} (rot : Equiv.Perm D)
    (flip : D → D) (tail : D → Prop) (a b c : D)
    (hb : UIBOTLocalPeanoNext rot flip tail a b)
    (hc : UIBOTLocalPeanoNext rot flip tail a c) : b = c := by
  classical
  unfold UIBOTLocalPeanoNext at hb hc
  split_ifs at hb hc with hfirst hsecond
  · obtain ⟨k, rfl, hk, hmin⟩ := hb
    obtain ⟨l, rfl, hl, hmin'⟩ := hc
    have he : k = l := by
      rcases lt_trichotomy k l with hlt | he | hgt
      · exact (hmin' k hlt hk).elim
      · exact he
      · exact (hmin l hgt hl).elim
    rw [he]
  · exact hb.trans hc.symm
  · exact hb.trans hc.symm

/-- Helper toward Proposition 3.9: the local successor rule transports
under rotation-, reversal-, and orientation-preserving dart equivalences.
The first-outgoing search keeps its same finite witness and minimality. -/
theorem uibotLocalPeanoNext_equiv {D E : Type*}
    (rot : Equiv.Perm D) (rot' : Equiv.Perm E)
    (flip : D → D) (flip' : E → E) (tail : D → Prop) (tail' : E → Prop)
    (e : D ≃ E)
    (hrot : ∀ d, e (rot d) = rot' (e d))
    (hflip : ∀ d, e (flip d) = flip' (e d))
    (htail : ∀ d, tail' (e d) ↔ tail d) (a b : D)
    (h : UIBOTLocalPeanoNext rot flip tail a b) :
    UIBOTLocalPeanoNext rot' flip' tail' (e a) (e b) := by
  classical
  have hinv (x : D) : e (rot.symm x) = rot'.symm (e x) := by
    apply rot'.injective
    rw [← hrot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hpow (k : ℕ) (x : D) : e ((rot ^ k) x) = (rot' ^ k) (e x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [pow_succ', Equiv.Perm.mul_apply, hrot, ih]
  unfold UIBOTLocalPeanoNext at h ⊢
  simp only [← hflip, ← hinv, ← hrot, ← hpow, htail]
  split_ifs at h ⊢ with hf hr
  · obtain ⟨k, he, hb, hmin⟩ := h
    exact ⟨k, congrArg e he, hb, hmin⟩
  · exact congrArg e h
  · exact congrArg e h

/-- Helper toward Proposition 3.9: the exact finite Peano successor is
given by the local rule. The descent search terminates in the finite terminal
star; the other two cases require only the displayed adjacent darts. -/
theorem uibotLocalPeanoNext_peano
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ ρ : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ ρ) (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    UIBOTLocalPeanoNext B.map.toCombinatorialMap.rot
      B.map.toCombinatorialMap.edgeInv B.map.tail
      (peanoEdge B ⟨j, by omega⟩) (peanoEdge B ⟨j + 1, hj⟩) := by
  classical
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  let rot := B.map.toCombinatorialMap.rot
  let flip := B.map.toCombinatorialMap.edgeInv
  have ha : B.map.tail a := peanoEdge_forward B _
  have hb : B.map.tail b := peanoEdge_forward B _
  have h := peanoStepKind_config B j hj
  have hcode := uibotLocalCodeLetter_peano B j hj
  change uibotLocalCodeLetter rot flip B.map.tail a = _ at hcode
  change UIBOTLocalPeanoNext rot flip B.map.tail a b
  cases hk : peanoStepKind B j hj with
  | descend =>
      rw [hk] at h
      obtain ⟨hs, ht, hsel, hbsel⟩ := h
      change b = rightmostOutgoing B (dartHeadVertex B.map a) ht at hbsel
      have hf : B.map.tail (rot.symm (flip a)) := by
        rw [hsel]
        exact (leftmostIncoming_internal_characterization B _ hs ht).2.2.1
      have hn : ¬ B.map.tail (flip a) :=
        (B.map.tail_iff a (B.noMissingDarts a)).1 ha
      have hvb : dartTailVertex B.map b = dartHeadVertex B.map a := by
        rw [hbsel]
        exact (rightmostOutgoing_internal_characterization B _ hs ht).1
      have hcycle : rot.SameCycle (flip a) b := Quotient.exact hvb.symm
      obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
      have hex : ∃ k : ℕ, B.map.tail ((rot ^ k) (flip a)) := ⟨k, hk.symm ▸ hb⟩
      let k := Nat.find hex
      have hk : B.map.tail ((rot ^ k) (flip a)) := Nat.find_spec hex
      have hkpos : 0 < k := by
        by_contra hnot
        have he : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hnot)
        simp only [he, pow_zero, Equiv.Perm.one_apply] at hk
        exact hn hk
      have hmin : ∀ l : ℕ, l < k → ¬ B.map.tail ((rot ^ l) (flip a)) :=
        fun l hl => Nat.find_min hex hl
      have hv : dartTailVertex B.map ((rot ^ k) (flip a)) =
          dartHeadVertex B.map a := by
        apply Quotient.sound
        exact (show rot.SameCycle (flip a) ((rot ^ k) (flip a)) from
          ⟨(k : ℤ), by simp only [zpow_natCast]⟩).symm
      have hpred : rot.symm ((rot ^ k) (flip a)) =
          (rot ^ (k - 1)) (flip a) := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
        rw [hm]
        simp only [Nat.succ_sub_one, pow_succ', Equiv.Perm.mul_apply,
          Equiv.symm_apply_apply]
      have he : (rot ^ k) (flip a) = b := by
        rw [hbsel]
        apply (rightmostOutgoing_internal_characterization B _ hs ht).2.2.2 _ hv hk
        change ¬ B.map.tail (rot.symm ((rot ^ k) (flip a)))
        rw [hpred]
        exact hmin (k - 1) (by omega)
      simp only [UIBOTLocalPeanoNext, hf, ite_eq_left]
      exact ⟨k, he.symm, hb, hmin⟩
  | rotate =>
      rw [hk] at h hcode
      obtain ⟨he, _, _, _, _, _⟩ := h
      have hr : B.map.tail (rot a) := he ▸ hb
      have hf : ¬ B.map.tail (rot.symm (flip a)) := by
        intro hf
        simp only [uibotLocalCodeLetter, hf, ite_eq_left] at hcode
        norm_num [PeanoStepKind.increment, stepCode] at hcode
      simp only [UIBOTLocalPeanoNext, hf, hr, ite_eq_left]
      exact he
  | climb =>
      rw [hk] at h hcode
      obtain ⟨_, _, _, _, _, _, he, _, _⟩ := h
      have hf : ¬ B.map.tail (rot.symm (flip a)) := by
        intro hf
        simp only [uibotLocalCodeLetter, hf, ite_eq_left] at hcode
        norm_num [PeanoStepKind.increment, stepCode] at hcode
      have hr : ¬ B.map.tail (rot a) := by
        intro hr
        simp only [uibotLocalCodeLetter, hf, hr, ite_eq_left] at hcode
        norm_num [PeanoStepKind.increment, stepCode] at hcode
      simp only [UIBOTLocalPeanoNext, hf, hr]
      exact he

/-- Helper toward Proposition 3.9: every nonfinal letter of a finite
forward KMSW code is recovered locally at the same chronological Peano index
in every representative of its procedure class. -/
theorem uibotLocalCodeLetter_forwardCode {ℓ ρ n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = kmswProcedureEquiv ℓ ρ n hn c)
    (j : ℕ) (hj : j + 1 < n) :
    uibotLocalCodeLetter R.B.map.toCombinatorialMap.rot
      R.B.map.toCombinatorialMap.edgeInv R.B.map.tail
      (peanoEdge R.B ⟨j, by simpa only [R.edges] using Nat.lt_of_succ_lt hj⟩) =
        codeExtend c j := by
  rw [uibotLocalCodeLetter_inverseCode R j hj,
    ← codeExtend_kmswRepInverseWalkClass R j hj,
    uibotPeano_inverseWalkClass_eq hn c R hR]

/-- Helper toward Proposition 3.9: in an admissible finite KMSW final
stage, the local rule at the actual chronological active dart recovers the
original input letter, without a supplied representative or recovery premise. -/
theorem uibotLocalCodeLetter_finalStage {ℓ ρ n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ ρ n) (j : ℕ) (hj : j + 1 < n) :
    let M := kmswStageDirectedMap (codeExtend c) (n - 1)
    let d : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
      (⟨act (codeExtend c) j, act_lt_nextEdge _ (by omega)⟩, false)
    uibotLocalCodeLetter M.rot M.edgeInv M.tail d = codeExtend c j := by
  let R := kmswWalkClassRep hn c
  obtain ⟨I, hI⟩ := uibotPeano_stageMapIso_exists hn c R rfl
  let M := kmswStageDirectedMap (codeExtend c) (n - 1)
  let d : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
    (⟨act (codeExtend c) j, act_lt_nextEdge _ (by omega)⟩, false)
  have hd : I.toEquiv d =
      peanoEdge R.B ⟨j, by simpa only [R.edges] using Nat.lt_of_succ_lt hj⟩ :=
    hI ⟨j, by omega⟩
  have he := uibotLocalCodeLetter_equiv M.rot R.B.map.rot
    M.edgeInv R.B.map.edgeInv M.tail R.B.map.tail I.toEquiv
    I.rot_comm I.edgeInv_comm I.tail_iff d
  rw [hd] at he
  exact he.symm.trans (uibotLocalCodeLetter_forwardCode hn c R rfl j hj)

/-- Helper toward Proposition 3.9: the local successor rule advances
from one actual chronological active dart to the next in an admissible finite
final stage. There is no assumed Peano or chronological identification. -/
theorem uibotLocalPeanoNext_finalStage {ℓ ρ n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ ρ n) (j : ℕ) (hj : j + 1 < n) :
    let M := kmswStageDirectedMap (codeExtend c) (n - 1)
    let a : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
      (⟨act (codeExtend c) j, act_lt_nextEdge _ (by omega)⟩, false)
    let b : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
      (⟨act (codeExtend c) (j + 1), act_lt_nextEdge _ (by omega)⟩, false)
    UIBOTLocalPeanoNext M.rot M.edgeInv M.tail a b := by
  let R := kmswWalkClassRep hn c
  obtain ⟨I, hI⟩ := uibotPeano_stageMapIso_exists hn c R rfl
  let M := kmswStageDirectedMap (codeExtend c) (n - 1)
  let a : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
    (⟨act (codeExtend c) j, act_lt_nextEdge _ (by omega)⟩, false)
  let b : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
    (⟨act (codeExtend c) (j + 1), act_lt_nextEdge _ (by omega)⟩, false)
  have ha : I.toEquiv a =
      peanoEdge R.B ⟨j, by simpa only [R.edges] using Nat.lt_of_succ_lt hj⟩ :=
    hI ⟨j, by omega⟩
  have hb : I.toEquiv b =
      peanoEdge R.B ⟨j + 1, by simpa only [R.edges] using hj⟩ := hI ⟨j + 1, hj⟩
  have h := uibotLocalPeanoNext_equiv R.B.map.rot M.rot
    R.B.map.edgeInv M.edgeInv R.B.map.tail M.tail I.symm.toEquiv
    I.symm.rot_comm I.symm.edgeInv_comm I.symm.tail_iff _ _
    (uibotLocalPeanoNext_peano R.B j (by simpa only [R.edges] using hj))
  rw [← ha, ← hb] at h
  change UIBOTLocalPeanoNext M.rot M.edgeInv M.tail
    (I.toEquiv.symm (I.toEquiv a)) (I.toEquiv.symm (I.toEquiv b)) at h
  simpa only [Equiv.symm_apply_apply] using h







































end DirectedDistances.PaperProofs.Section3

end
