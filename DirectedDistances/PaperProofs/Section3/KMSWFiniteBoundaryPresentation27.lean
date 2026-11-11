/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation26

 

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

private theorem kmswStageFiniteBoundaryPresentation27_index_of_nonempty_side
    {V E : Type*} {M : DirectedPlaneMapWithMissing V E}
    (Q : InfiniteBoundaryPresentation M) (c : Fin 4)
    (hn : sideNonempty Q c) :
    ∃ i : InfiniteBoundaryDartIndex Q, sideTag Q i = c := by
  fin_cases c
  · simp only [sideNonempty, Fin.val_zero, ↓reduceIte] at hn
    rcases hn with ⟨i⟩
    exact ⟨.upperLeft i, rfl⟩
  · simp only [sideNonempty, Fin.val_one, ↓reduceIte] at hn
    rcases hn with ⟨i⟩
    exact ⟨.upperRight i, rfl⟩
  · simp only [sideNonempty, Fin.val_ofNat, ↓reduceIte] at hn
    rcases hn with ⟨i⟩
    exact ⟨.lowerRight i, rfl⟩
  · simp only [sideNonempty, Fin.val_ofNat, ↓reduceIte] at hn
    rcases hn with ⟨i⟩
    exact ⟨.lowerLeft i, rfl⟩

private theorem kmswStageFiniteBoundaryPresentation27_sideDistance_self
    (a : Fin 4) : sideDistance a a = 0 := by
  unfold sideDistance
  have h : a.val + 4 - a.val = 4 := by omega
  rw [h, Nat.mod_self]

private theorem kmswStageFiniteBoundaryPresentation27_sideDistance_eq_sub
    {a b : Fin 4} (hab : a.val < b.val) :
    sideDistance a b = b.val - a.val := by
  unfold sideDistance
  rw [show b.val + 4 - a.val = (b.val - a.val) + 4 by omega,
    Nat.add_mod]
  simp [Nat.mod_eq_of_lt (by omega : b.val - a.val < 4)]

private theorem kmswStageFiniteBoundaryPresentation27_sideDistance_eq_wrap
    {a c : Fin 4} (hca : c.val < a.val) :
    sideDistance a c = c.val + 4 - a.val := by
  unfold sideDistance
  exact Nat.mod_eq_of_lt (by omega)

private theorem kmswStageFiniteBoundaryPresentation27_sideDistance_between
    {a b c : Fin 4} (hab : a.val < b.val)
    (h₁ : 0 < sideDistance a c)
    (h₂ : sideDistance a c < sideDistance a b) :
    a.val < c.val ∧ c.val < b.val := by
  have hdb := kmswStageFiniteBoundaryPresentation27_sideDistance_eq_sub hab
  by_cases hac : a.val < c.val
  · have hdc := kmswStageFiniteBoundaryPresentation27_sideDistance_eq_sub hac
    rw [hdc, hdb] at h₂
    exact ⟨hac, by omega⟩
  · have hle : c.val ≤ a.val := Nat.le_of_not_gt hac
    have hneq : c.val ≠ a.val := by
      intro heq
      have heq' : a = c := Fin.ext heq.symm
      rw [heq'] at h₁
      rw [kmswStageFiniteBoundaryPresentation27_sideDistance_self] at h₁
      omega
    have hca : c.val < a.val := by omega
    have hdc := kmswStageFiniteBoundaryPresentation27_sideDistance_eq_wrap hca
    rw [hdc, hdb] at h₂
    omega

private theorem kmswStageFiniteBoundaryPresentation27_wrapDistance_between
    {a c : Fin 4} (ha : 2 ≤ a.val)
    (h₁ : 0 < sideDistance a c)
    (h₂ : sideDistance a c < sideDistance a 0) :
    a.val < c.val := by
  by_contra hac
  have hle : c.val ≤ a.val := Nat.le_of_not_gt hac
  by_cases heq : c.val = a.val
  · have heq' : a = c := Fin.ext heq.symm
    rw [heq'] at h₁
    rw [kmswStageFiniteBoundaryPresentation27_sideDistance_self] at h₁
    omega
  · have hca : c.val < a.val := by omega
    have hdc := kmswStageFiniteBoundaryPresentation27_sideDistance_eq_wrap hca
    have hd0 : sideDistance a 0 = 4 - a.val := by
      unfold sideDistance
      change (4 - a.val) % 4 = 4 - a.val
      exact Nat.mod_eq_of_lt (by omega)
    rw [hdc, hd0] at h₂
    omega

/-- Helper toward Definition 3.2: a geometric successor is either the next
dart on the same side or the first dart of the next nonempty side. -/
theorem kmswStageFiniteBoundaryPresentation27_successor_classification
    (w : ℕ → Fin 3) (n : ℕ) (P : StageDrawing w n)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex))
    (hreal : kmsw_stage_map_realization32 w n P M)
    (i j : InfiniteBoundaryDartIndex
      (kmswStageFiniteBoundaryPresentation w n M J))
    (hsucc : (stageRot w n).symm
        (edgeFlip _ (InfiniteBoundaryDartIndex.dart
          (kmswStageFiniteBoundaryPresentation w n M J) i)) =
      InfiniteBoundaryDartIndex.dart
        (kmswStageFiniteBoundaryPresentation w n M J) j) :
    sideNext (kmswStageFiniteBoundaryPresentation w n M J) i = some j ∨
      (sideNext (kmswStageFiniteBoundaryPresentation w n M J) i = none ∧
        firstOnSide (kmswStageFiniteBoundaryPresentation w n M J) j ∧
        nextNonemptySide (kmswStageFiniteBoundaryPresentation w n M J)
          (sideTag (kmswStageFiniteBoundaryPresentation w n M J) i)
          (sideTag (kmswStageFiniteBoundaryPresentation w n M J) j)) := by
  let Q := kmswStageFiniteBoundaryPresentation w n M J
  let pos := kmswStageFiniteBoundaryPresentation21_position w n M J
  have hpos :=
    (kmswStageFiniteBoundaryPresentation21_successor_iff w n M J i j).mp hsucc
  have hlen : 0 < (stageOuterWord w n).length :=
    List.length_pos_iff.mpr (stageOuterWord_nonempty w n)
  have hpi : (pos i).val < (stageOuterWord w n).length := (pos i).isLt
  have hsum : (pos i).val + 1 ≤ (stageOuterWord w n).length := by omega
  have hinj : Function.Injective pos :=
    (kmswStageFiniteBoundaryPresentation21_position_bijective w n M J).1
  have hstep := kmswStageFiniteBoundaryPresentation21_side_step w n M J
  have htagmono := kmswStageFiniteBoundaryPresentation21_tag_mono w n M J
  by_cases hnowrap : (pos i).val + 1 < (stageOuterWord w n).length
  · have hval : (pos j).val = (pos i).val + 1 := by
      have hv := congrArg Fin.val hpos
      dsimp [boundaryCycleSucc4] at hv
      rw [Nat.mod_eq_of_lt hnowrap] at hv
      exact hv
    have hposij : (pos i).val < (pos j).val := by rw [hval]; omega
    by_cases htags : sideTag Q i = sideTag Q j
    · exact Or.inl ((hstep i j).mpr ⟨htags, hval⟩)
    · right
      have hnone : sideNext Q i = none := by
        cases hs : sideNext Q i with
        | none => rfl
        | some k =>
          have hk := (hstep i k).mp hs
          have hkj : k = j := hinj (Fin.ext (hk.2.trans hval.symm))
          exact (htags (hk.1.trans (congrArg (sideTag Q) hkj))).elim
      have hfirst : firstOnSide Q j := by
        change ∀ k, sideNext Q k ≠ some j
        intro k hk
        have hk' := (hstep k j).mp hk
        have hki : k = i := hinj (Fin.ext (Nat.add_right_cancel
          (hk'.2.symm.trans hval)))
        exact (htags ((congrArg (sideTag Q) hki).symm.trans hk'.1)).elim
      have hnonj : sideNonempty Q (sideTag Q j) := by
        cases j with
        | upperLeft x => exact ⟨x⟩
        | upperRight x => exact ⟨x⟩
        | lowerRight x => exact ⟨x⟩
        | lowerLeft x => exact ⟨x⟩
      have hmono : (sideTag Q i).val ≤ (sideTag Q j).val :=
        htagmono i j (Nat.le_of_lt hposij)
      have htaglt : (sideTag Q i).val < (sideTag Q j).val := by
        have hne : (sideTag Q i).val ≠ (sideTag Q j).val := by
          intro heq
          exact htags (Fin.ext heq)
        omega
      have hdist : sideDistance (sideTag Q i) (sideTag Q j) =
          (sideTag Q j).val - (sideTag Q i).val := by
        exact kmswStageFiniteBoundaryPresentation27_sideDistance_eq_sub htaglt
      have hdistpos : 0 < sideDistance (sideTag Q i) (sideTag Q j) := by
        rw [hdist]
        omega
      have hintervening : ∀ c : Fin 4,
          0 < sideDistance (sideTag Q i) c →
          sideDistance (sideTag Q i) c <
            sideDistance (sideTag Q i) (sideTag Q j) →
          ¬ sideNonempty Q c := by
        intro c hca hcb hn
        obtain ⟨k, hkc⟩ :=
          kmswStageFiniteBoundaryPresentation27_index_of_nonempty_side Q c hn
        have hbetween := kmswStageFiniteBoundaryPresentation27_sideDistance_between
          htaglt hca hcb
        have hci := hbetween.1
        have hcj := hbetween.2
        have hki : (pos i).val < (pos k).val := by
          by_contra hnot
          have hle := htagmono k i (Nat.le_of_not_gt hnot)
          rw [hkc] at hle
          exact (Nat.not_lt_of_ge hle hci).elim
        have hkj : (pos k).val < (pos j).val := by
          by_contra hnot
          have hle := htagmono j k (Nat.le_of_not_gt hnot)
          rw [hkc] at hle
          exact (Nat.not_lt_of_ge hle hcj).elim
        have hgap₁ : (pos i).val + 1 ≤ (pos k).val := Nat.succ_le_of_lt hki
        have hgap₂ : (pos k).val + 1 ≤ (pos j).val := Nat.succ_le_of_lt hkj
        rw [hval] at hgap₂
        omega
      exact And.intro hnone (And.intro hfirst
        (And.intro hnonj (And.intro hdistpos hintervening)))
  · have hlast : (pos i).val + 1 = (stageOuterWord w n).length := by omega
    have hjzero : (pos j).val = 0 := by
      have hv := congrArg Fin.val hpos
      dsimp [boundaryCycleSucc4] at hv
      rw [hlast, Nat.mod_self] at hv
      exact hv
    have hULlen : 0 < (kmswStageULDartRun w n).length :=
      List.length_pos_iff.mpr
        (kmswStageFiniteBoundaryPresentation5_upperLeftRun_ne_nil w n)
    have hLRlen : 0 < (kmswStageLRDartRun w n).length :=
      List.length_pos_iff.mpr
        (kmswStageFiniteBoundaryPresentation5_lowerRightRun_ne_nil w n)
    let u : InfiniteBoundaryDartIndex Q := .upperLeft ⟨0, hULlen⟩
    let r : InfiniteBoundaryDartIndex Q := .lowerRight ⟨0, hLRlen⟩
    have hu : (pos u).val = 0 := by
      simp [u, pos, kmswStageFiniteBoundaryPresentation21_position,
        kmswStageFiniteBoundaryPresentation, kmswFiniteRunSide]
    have hj : j = u := hinj (Fin.ext (by rw [hjzero, hu]))
    have htagj : sideTag Q j = 0 := by rw [hj]; rfl
    have hnonj : sideNonempty Q (sideTag Q j) := by
      rw [htagj]
      exact ⟨⟨0, hULlen⟩⟩
    have hrlt : (pos r).val < (stageOuterWord w n).length := (pos r).isLt
    have hri : (pos r).val ≤ (pos i).val := by omega
    have htagi_lower : 2 ≤ (sideTag Q i).val := by
      have hle := htagmono r i hri
      simpa [r, sideTag] using hle
    have hnone : sideNext Q i = none := by
      cases hs : sideNext Q i with
      | none => rfl
      | some k =>
        have hk := (hstep i k).mp hs
        have : (pos k).val = (stageOuterWord w n).length := by
          calc
            (pos k).val = (pos i).val + 1 := hk.2
            _ = (stageOuterWord w n).length := hlast
        exact (Nat.ne_of_lt (pos k).isLt this).elim
    have hfirst : firstOnSide Q j := by
      change ∀ k, sideNext Q k ≠ some j
      intro k hk
      have hk' := (hstep k j).mp hk
      have : (pos k).val + 1 = 0 := by
        rw [← hjzero]
        exact hk'.2.symm
      omega
    have hdistpos : 0 < sideDistance (sideTag Q i) (sideTag Q j) := by
      rw [htagj]
      have hdist : sideDistance (sideTag Q i) 0 =
          4 - (sideTag Q i).val := by
        unfold sideDistance
        change (4 - (sideTag Q i).val) % 4 = 4 - (sideTag Q i).val
        exact Nat.mod_eq_of_lt (by omega)
      rw [hdist]
      omega
    have hintervening : ∀ c : Fin 4,
        0 < sideDistance (sideTag Q i) c →
        sideDistance (sideTag Q i) c <
          sideDistance (sideTag Q i) (sideTag Q j) →
        ¬ sideNonempty Q c := by
      intro c hca hcb hn
      obtain ⟨k, hkc⟩ :=
        kmswStageFiniteBoundaryPresentation27_index_of_nonempty_side Q c hn
      rw [htagj] at hcb
      have hci := kmswStageFiniteBoundaryPresentation27_wrapDistance_between
        htagi_lower hca hcb
      have hik : (pos i).val < (pos k).val := by
        by_contra hnot
        have hle := htagmono k i (Nat.le_of_not_gt hnot)
        rw [hkc] at hle
        exact (Nat.not_lt_of_ge hle hci).elim
      have hklt : (pos k).val < (stageOuterWord w n).length := (pos k).isLt
      omega
    apply Or.inr
    exact And.intro hnone (And.intro hfirst
      (And.intro hnonj (And.intro hdistpos hintervening)))










































































































end DirectedDistances.PaperProofs.Section3

end
