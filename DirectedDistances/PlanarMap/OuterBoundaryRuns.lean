/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.OuterBoundary

/-! # Uniqueness of the outer-boundary missing runs

On the domain where both present arcs are nonempty, the four consecutive
blocks of an outer-boundary witness have cuts determined by their dart -/

public section
namespace DirectedDistances.PlanarMap

open List

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
private theorem rotate_indices_eq_of_same_head {xs : List D}
    (hnodup : xs.Nodup) (hne : xs ≠ []) {i j : ℕ}
    (hhead : (xs.rotate i).head? = (xs.rotate j).head?) :
    i % xs.length = j % xs.length := by
  have h := hhead
  rw [← List.rotate_mod xs i, ← List.rotate_mod xs j] at h
  simpa only [List.head?_rotate, Nat.mod_lt, List.length_pos_of_ne_nil hne,
    List.getElem?_eq_getElem, Option.some_inj, hnodup.getElem_inj_iff,
    Fin.ext_iff] using h

omit [Fintype D] [DecidableEq D] in
private theorem takeWhile_append_of_all {p : D → Bool} {xs ys : List D}
    (hall : ∀ x ∈ xs, p x = true) (hstop : List.takeWhile p ys = []) :
    List.takeWhile p (xs ++ ys) = xs := by
  induction xs with
  | nil => simpa using hstop
  | cons a xs ih =>
      have ha := hall a (by simp)
      have htail : ∀ x ∈ xs, p x = true := by
        intro x hx
        exact hall x (by simp [hx])
      simp only [List.cons_append]
      rw [List.takeWhile_cons]
      simp [ha, ih htail]

omit [Fintype D] [DecidableEq D] in
private theorem take_ne_nil_of_pos {xs : List D} {n : ℕ}
    (hn : 0 < n) (hx : xs ≠ []) : xs.take n ≠ [] := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons a as =>
      cases n with
      | zero => omega
      | succ n => simp

/-- Two four-arc witnesses have the same four ordered blocks when both
present arcs are nonempty (defn:bound-edges,
this uniqueness statement because adjacent missing blocks can then share a
cut. -/
theorem fourArcsWitness_unique_blocks (M : DirectedMapWithMissing D)
    (B C : NonemptyWord D) (ul ur lr ll ul' ur' lr' ll' : List D)
    (hUL : M.ulDarts.Nonempty) (hLR : M.lrDarts.Nonempty)
    (hB : FourArcsWitness M B ul ur lr ll)
    (hC : FourArcsWitness M C ul' ur' lr' ll') :
    ur = ur' ∧ ll = ll' ∧ ul = ul' ∧ lr = lr' := by
  classical
  let w := ul ++ (ur ++ lr ++ ll)
  let w' := ul' ++ (ur' ++ lr' ++ ll')
  have hwrot : w ~r w' := by
    simpa [w, w', List.append_assoc] using hB.2.1.symm.trans
      ((isOuterCycle_unique_up_to_rotation M B C hB.1 hC.1).trans hC.2.1)
  have hwnodup : w.Nodup := by
    simpa [w, List.append_assoc] using (hB.2.1.nodup_iff).mp B.nodup
  have hul_ne : ul ≠ [] := by
    intro h
    obtain ⟨d, hd⟩ := hUL
    have hmem : d ∈ ul := (hB.2.2.1 d).mpr hd
    simp [h] at hmem
  have hlr_ne : lr ≠ [] := by
    intro h
    obtain ⟨d, hd⟩ := hLR
    have hmem : d ∈ lr := (hB.2.2.2.1 d).mpr hd
    simp [h] at hmem
  have htail_ne : ur ++ lr ++ ll ≠ [] := by
    simp [hlr_ne]
  have hw_ne : w ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp [w, List.length_append] at hlen
    have : ul = [] := by
      cases ul with
      | nil => rfl
      | cons a as => simp at hlen
    exact hul_ne this
  have hdisj : List.Disjoint ul (ur ++ lr ++ ll) := by
    apply List.disjoint_of_nodup_append
    simpa [w, List.append_assoc] using hwnodup
  have hlast_tail : w.getLast hw_ne ∈ ur ++ lr ++ ll := by
    have hlast_eq : w.getLast hw_ne = (ur ++ lr ++ ll).getLast htail_ne :=
      List.getLast_append_of_right_ne_nil _ _ htail_ne
    rw [hlast_eq]
    exact List.getLast_mem htail_ne
  have hlast_not_ul : w.getLast hw_ne ∉ M.ulDarts := by
    intro h
    have hmem : w.getLast hw_ne ∈ ul := (hB.2.2.1 _).mpr h
    exact hdisj hmem hlast_tail
  have hul'_ne : ul' ≠ [] := by
    intro h
    obtain ⟨d, hd⟩ := hUL
    have hmem : d ∈ ul' := (hC.2.2.1 d).mpr hd
    simp [h] at hmem
  have hlr'_ne : lr' ≠ [] := by
    intro h
    obtain ⟨d, hd⟩ := hLR
    have hmem : d ∈ lr' := (hC.2.2.2.1 d).mpr hd
    simp [h] at hmem
  have htail'_ne : ur' ++ lr' ++ ll' ≠ [] := by
    simp [hlr'_ne]
  cases hul_eq : ul with
  | nil => exact (hul_ne hul_eq).elim
  | cons a as =>
      have ha_ul : a ∈ ul := by simp [hul_eq]
      have ha_outer : a ∈ M.ulDarts := (hB.2.2.1 a).mp ha_ul
      have ha_ul' : a ∈ ul' := (hC.2.2.1 a).mpr ha_outer
      have ha_w' : a ∈ w' := by simp [w', ha_ul']
      let j := w'.idxOf a
      have hj_lt' : j < w'.length := by
        dsimp [j]
        exact List.idxOf_lt_length_of_mem ha_w'
      have hj_lt_ul' : j < ul'.length := by
        have hjidx : j = ul'.idxOf a := by
          dsimp [j, w']
          simp only [List.append_assoc]
          exact List.idxOf_append_of_mem ha_ul'
        rw [hjidx]
        exact List.idxOf_lt_length_of_mem ha_ul'
      rcases hwrot with ⟨n, hn⟩
      have hhead0 : (w.rotate 0).head? = some a := by
        simp [w, hul_eq]
      have hheadj' : (w'.rotate j).head? = some a := by
        rw [List.head?_rotate hj_lt']
        simp [j, List.getElem?_idxOf ha_w']
      have hheadnj : (w.rotate (n + j)).head? = some a := by
        rw [← hn, List.rotate_rotate] at hheadj'
        exact hheadj'
      have hmod : 0 % w.length = (n + j) % w.length :=
        rotate_indices_eq_of_same_head hwnodup hw_ne (hhead0.trans hheadnj.symm)
      have hrotEq : w.rotate (n + j) = w'.rotate j := by
        rw [← hn, List.rotate_rotate]
      have hAligned : w.rotate 0 = w'.rotate j := by
        calc
          w.rotate 0 = w.rotate (n + j) := by
            rw [← List.rotate_mod w 0, ← List.rotate_mod w (n + j), hmod]
          _ = w'.rotate j := hrotEq
      have hj_zero : j = 0 := by
        by_contra hj0
        have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
        have htake_ne : ul'.take j ≠ [] := take_ne_nil_of_pos hj_pos hul'_ne
        have htakeW' : w'.take j = ul'.take j := by
          dsimp [w']
          simp only [List.append_assoc]
          exact List.take_append_of_le_length (Nat.le_of_lt hj_lt_ul')
        let x := (ul'.take j).getLast htake_ne
        have hx_ul' : x ∈ ul' := by
          have hx : x ∈ ul'.take j := List.getLast_mem htake_ne
          exact (List.take_sublist j ul').subset (by simp [x])
        have hx_outer : x ∈ M.ulDarts := (hC.2.2.1 x).mp hx_ul'
        have hW'_ne : w' ≠ [] := by
          intro h
          exact hw_ne ((List.rotate_eq_nil_iff.mp (hn.trans h)))
        have hrot_ne : w'.rotate j ≠ [] := by
          intro h
          exact hW'_ne (List.rotate_eq_nil_iff.mp h)
        have htake_ne' : w'.take j ≠ [] := by
          simpa [htakeW'] using htake_ne
        have hrotdecomp : w'.rotate j = w'.drop j ++ w'.take j :=
          List.rotate_eq_drop_append_take (Nat.le_of_lt hj_lt')
        have hlast_rot? : (w'.rotate j).getLast? = some x := by
          rw [hrotdecomp, List.getLast?_append_of_ne_nil _ htake_ne']
          simp [x, htakeW', List.getLast?_eq_getLast_of_ne_nil htake_ne]
        have hx_last : x = w.getLast hw_ne := by
          have hopt := congrArg List.getLast? hAligned
          have hopt' : some (w.getLast hw_ne) = some x := by
            rw [List.rotate_zero, List.getLast?_eq_getLast_of_ne_nil hw_ne,
              hlast_rot?] at hopt
            exact hopt
          exact (Option.some.inj hopt').symm
        have hbad : w.getLast hw_ne ∈ M.ulDarts := by
          rw [← hx_last]
          exact hx_outer
        exact hlast_not_ul hbad
      have hwords : w = w' := by
        simpa [hj_zero] using hAligned
      have hmiss_not_ul : ∀ d, M.missing d → d ∉ M.ulDarts := by
        intro d hm hu
        exact hu.1 hm
      have hlr_not_ul : ∀ d, d ∈ lr → d ∉ M.ulDarts := by
        intro d hd hu
        have hdlr : d ∈ M.lrDarts := (hB.2.2.2.1 d).mp hd
        exact hdlr.2.1 hu.2.1
      have hlr'_not_ul : ∀ d, d ∈ lr' → d ∉ M.ulDarts := by
        intro d hd hu
        have hdlr : d ∈ M.lrDarts := (hC.2.2.2.1 d).mp hd
        exact hdlr.2.1 hu.2.1
      let pUL : D → Bool := fun d => decide (d ∈ M.ulDarts)
      have htail_not_ul : ∀ d ∈ ur ++ lr ++ ll, d ∉ M.ulDarts := by
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · rcases List.mem_append.mp hd with hd | hd
          · exact hmiss_not_ul d (hB.2.2.2.2.1 d hd)
          · exact hlr_not_ul d hd
        · exact hmiss_not_ul d (hB.2.2.2.2.2 d hd)
      have htail'_not_ul : ∀ d ∈ ur' ++ lr' ++ ll', d ∉ M.ulDarts := by
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · rcases List.mem_append.mp hd with hd | hd
          · exact hmiss_not_ul d (hC.2.2.2.2.1 d hd)
          · exact hlr'_not_ul d hd
        · exact hmiss_not_ul d (hC.2.2.2.2.2 d hd)
      have hstopUL : List.takeWhile pUL (ur ++ lr ++ ll) = [] := by
        cases htail : ur ++ lr ++ ll with
        | nil => exact (htail_ne htail).elim
        | cons d ds =>
            have hdmem : d ∈ ur ++ lr ++ ll := by simp [htail]
            have hdnot : d ∉ M.ulDarts := htail_not_ul d hdmem
            simp [pUL, hdnot]
      have hstopUL' : List.takeWhile pUL (ur' ++ lr' ++ ll') = [] := by
        cases htail : ur' ++ lr' ++ ll' with
        | nil => exact (htail'_ne htail).elim
        | cons d ds =>
            have hdmem : d ∈ ur' ++ lr' ++ ll' := by simp [htail]
            have hdnot : d ∉ M.ulDarts := htail'_not_ul d hdmem
            simp [pUL, hdnot]
      have htakeUL : List.takeWhile pUL w = ul := by
        have hall : ∀ d ∈ ul, pUL d = true := by
          intro d hd
          simp [pUL, (hB.2.2.1 d).mp hd]
        rw [show w = ul ++ (ur ++ lr ++ ll) by simp [w, List.append_assoc]]
        exact takeWhile_append_of_all hall hstopUL
      have htakeUL' : List.takeWhile pUL w' = ul' := by
        have hall : ∀ d ∈ ul', pUL d = true := by
          intro d hd
          simp [pUL, (hC.2.2.1 d).mp hd]
        rw [show w' = ul' ++ (ur' ++ lr' ++ ll') by simp [w', List.append_assoc]]
        exact takeWhile_append_of_all hall hstopUL'
      have hul_eq' : ul = ul' := by
        calc
          ul = List.takeWhile pUL w := htakeUL.symm
          _ = List.takeWhile pUL w' := by rw [hwords]
          _ = ul' := htakeUL'
      have htail_eq : ur ++ lr ++ ll = ur' ++ lr' ++ ll' := by
        have hwords' : ul ++ (ur ++ lr ++ ll) = ul' ++ (ur' ++ lr' ++ ll') := by
          simpa [w, w', List.append_assoc] using hwords
        rw [hul_eq'] at hwords'
        exact (List.append_right_injective ul') hwords'
      have hmissing_not_lr : ∀ d, M.missing d → d ∉ M.lrDarts := by
        intro d hm hlr
        exact hlr.1 hm
      let pMiss : D → Bool := fun d => decide (M.missing d)
      have hstopMiss : List.takeWhile pMiss (lr ++ ll) = [] := by
        cases hlr_eq : lr with
        | nil => exact (hlr_ne hlr_eq).elim
        | cons d ds =>
            have hd_lr : d ∈ M.lrDarts :=
              (hB.2.2.2.1 d).mp (by simp [hlr_eq])
            have hnot : ¬ M.missing d := by
              intro hm
              exact (hmissing_not_lr d hm) hd_lr
            simp [pMiss, hnot]
      have hstopMiss' : List.takeWhile pMiss (lr' ++ ll') = [] := by
        cases hlr'_eq : lr' with
        | nil => exact (hlr'_ne hlr'_eq).elim
        | cons d ds =>
            have hd_lr : d ∈ M.lrDarts :=
              (hC.2.2.2.1 d).mp (by simp [hlr'_eq])
            have hnot : ¬ M.missing d := by
              intro hm
              exact (hmissing_not_lr d hm) hd_lr
            simp [pMiss, hnot]
      have htakeUR : List.takeWhile pMiss (ur ++ lr ++ ll) = ur := by
        have hall : ∀ d ∈ ur, pMiss d = true := by
          intro d hd
          simp [pMiss, hB.2.2.2.2.1 d hd]
        simpa only [List.append_assoc] using
          (takeWhile_append_of_all hall hstopMiss)
      have htakeUR' : List.takeWhile pMiss (ur' ++ lr' ++ ll') = ur' := by
        have hall : ∀ d ∈ ur', pMiss d = true := by
          intro d hd
          simp [pMiss, hC.2.2.2.2.1 d hd]
        simpa only [List.append_assoc] using
          (takeWhile_append_of_all hall hstopMiss')
      have hur_eq : ur = ur' := by
        calc
          ur = List.takeWhile pMiss (ur ++ lr ++ ll) := htakeUR.symm
          _ = List.takeWhile pMiss (ur' ++ lr' ++ ll') := by rw [htail_eq]
          _ = ur' := htakeUR'
      have hlrll_eq : lr ++ ll = lr' ++ ll' := by
        have h := htail_eq
        rw [hur_eq] at h
        have h' : ur' ++ (lr ++ ll) = ur' ++ (lr' ++ ll') := by
          simpa [List.append_assoc] using h
        exact (List.append_right_injective ur') h'
      let pLR : D → Bool := fun d => decide (d ∈ M.lrDarts)
      have hstopLR : List.takeWhile pLR ll = [] := by
        cases hll : ll with
        | nil => rfl
        | cons d ds =>
            have hm : M.missing d := hB.2.2.2.2.2 d (by simp [hll])
            have hnot := hmissing_not_lr d hm
            simp [pLR, hnot]
      have hstopLR' : List.takeWhile pLR ll' = [] := by
        cases hll : ll' with
        | nil => rfl
        | cons d ds =>
            have hm : M.missing d := hC.2.2.2.2.2 d (by simp [hll])
            have hnot := hmissing_not_lr d hm
            simp [pLR, hnot]
      have htakeLR : List.takeWhile pLR (lr ++ ll) = lr := by
        have hall : ∀ d ∈ lr, pLR d = true := by
          intro d hd
          simp [pLR, (hB.2.2.2.1 d).mp hd]
        exact takeWhile_append_of_all hall hstopLR
      have htakeLR' : List.takeWhile pLR (lr' ++ ll') = lr' := by
        have hall : ∀ d ∈ lr', pLR d = true := by
          intro d hd
          simp [pLR, (hC.2.2.2.1 d).mp hd]
        exact takeWhile_append_of_all hall hstopLR'
      have hlr_eq' : lr = lr' := by
        calc
          lr = List.takeWhile pLR (lr ++ ll) := htakeLR.symm
          _ = List.takeWhile pLR (lr' ++ ll') := by rw [hlrll_eq]
          _ = lr' := htakeLR'
      have hll_eq : ll = ll' := by
        have h := hlrll_eq
        rw [hlr_eq'] at h
        have h' : lr' ++ ll = lr' ++ ll' := by simpa [List.append_assoc] using h
        exact (List.append_right_injective lr') h'
      exact ⟨hur_eq, hll_eq, (by simpa [hul_eq] using hul_eq'), hlr_eq'⟩

/-- UR membership agrees across witnesses on the nonempty-present-arc -/
theorem mem_ur_iff_of_fourArcsWitnesses (M : DirectedMapWithMissing D)
    (B C : NonemptyWord D) (ul ur lr ll ul' ur' lr' ll' : List D)
    (hUL : M.ulDarts.Nonempty) (hLR : M.lrDarts.Nonempty)
    (hB : FourArcsWitness M B ul ur lr ll)
    (hC : FourArcsWitness M C ul' ur' lr' ll') (d : D) :
    d ∈ ur ↔ d ∈ ur' := by
  have heq := fourArcsWitness_unique_blocks M B C ul ur lr ll ul' ur' lr' ll'
    hUL hLR hB hC
  rw [heq.1]

/-- LL membership agrees across witnesses on the nonempty-present-arc -/
theorem mem_ll_iff_of_fourArcsWitnesses (M : DirectedMapWithMissing D)
    (B C : NonemptyWord D) (ul ur lr ll ul' ur' lr' ll' : List D)
    (hUL : M.ulDarts.Nonempty) (hLR : M.lrDarts.Nonempty)
    (hB : FourArcsWitness M B ul ur lr ll)
    (hC : FourArcsWitness M C ul' ur' lr' ll') (d : D) :
    d ∈ ll ↔ d ∈ ll' := by
  have heq := fourArcsWitness_unique_blocks M B C ul ur lr ll ul' ur' lr' ll'
    hUL hLR hB hC
  rw [heq.2.1]

/-- The existentially defined UR set can be read from any fixed witness when
both present arcs are nonempty (defn:bound-edges, -/
theorem mem_urDarts_iff_of_witness (M : DirectedMapWithMissing D)
    (hUL : M.ulDarts.Nonempty) (hLR : M.lrDarts.Nonempty)
    (B : NonemptyWord D) (ul ur lr ll : List D)
    (hB : FourArcsWitness M B ul ur lr ll) (d : D) :
    d ∈ urDarts M ↔ d ∈ ur := by
  constructor
  · intro hd
    rcases hd with ⟨C, ul', ur', lr', ll', hC, hdur'⟩
    have heq := fourArcsWitness_unique_blocks M B C ul ur lr ll ul' ur' lr' ll'
      hUL hLR hB hC
    simpa [heq.1] using hdur'
  · intro hd
    exact ⟨B, ul, ur, lr, ll, hB, hd⟩

/-- The existentially defined LL set can be read from any fixed witness when
both present arcs are nonempty (defn:bound-edges, -/
theorem mem_llDarts_iff_of_witness (M : DirectedMapWithMissing D)
    (hUL : M.ulDarts.Nonempty) (hLR : M.lrDarts.Nonempty)
    (B : NonemptyWord D) (ul ur lr ll : List D)
    (hB : FourArcsWitness M B ul ur lr ll) (d : D) :
    d ∈ llDarts M ↔ d ∈ ll := by
  constructor
  · intro hd
    rcases hd with ⟨C, ul', ur', lr', ll', hC, hdll'⟩
    have heq := fourArcsWitness_unique_blocks M B C ul ur lr ll ul' ur' lr' ll'
      hUL hLR hB hC
    simpa [heq.2.1] using hdll'
  · intro hd
    exact ⟨B, ul, ur, lr, ll, hB, hd⟩

end DirectedDistances.PlanarMap
