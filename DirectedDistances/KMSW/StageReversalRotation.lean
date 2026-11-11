module

public import DirectedDistances.KMSW.StageReversalEdges
public import DirectedDistances.KMSW.StageReversalPhi
public import DirectedDistances.KMSW.StageSlotForest
public import DirectedDistances.KMSW.StageRotation
public import DirectedDistances.KMSW.StageReversalOrientationCheck
public import DirectedDistances.KMSW.StageFaceDetermination

import all DirectedDistances.KMSW.StageReversalEdges

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap




@[expose] noncomputable def kmswRevDart (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (d : StageDart (kmswStage wr n).nextEdge) :
    StageDart (kmswStage w n).nextEdge :=
  (⟨kmswRevEdge w wr n d.1.val, kmswRevEdge_mapsTo wr w n hrev d.1.isLt⟩, !d.2)




theorem kmswRevDart_apply (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (d : StageDart (kmswStage wr n).nextEdge) :
    kmswRevDart w wr n hrev d =
      (⟨kmswRevEdge w wr n d.1.val, kmswRevEdge_mapsTo wr w n hrev d.1.isLt⟩,
        !d.2) := rfl




theorem kmswRevDart_flip (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (d : StageDart (kmswStage wr n).nextEdge) :
    kmswRevDart w wr n hrev (edgeFlip _ d) = edgeFlip _ (kmswRevDart w wr n hrev d) :=
  rfl




theorem kmswRevDart_endpoint (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (d : StageDart (kmswStage wr n).nextEdge) :
    stageEndpoint (kmswStage w n) (kmswRevDart w wr n hrev d) =
      kmswReversalPhi wr w n (stageEndpoint (kmswStage wr n) d) := by
  obtain ⟨hw, he⟩ := kmswRevEdge_endpoints wr w n hrev d.1.val d.1.isLt
  rcases d with ⟨e, b⟩
  cases b
  · exact he
  · exact hw




theorem kmswRevDart_inverse (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (d : StageDart (kmswStage wr n).nextEdge) :
    kmswRevDart wr w n (kmswReversal_letters_symm wr w n hrev)
      (kmswRevDart w wr n hrev d) = d := by
  apply Prod.ext
  · apply Fin.ext
    exact kmswRevEdge_inverse wr w n hrev d.1.val d.1.isLt
  · exact Bool.not_not d.2




@[expose] noncomputable def kmswRevDartEquiv (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    StageDart (kmswStage wr n).nextEdge ≃ StageDart (kmswStage w n).nextEdge where
  toFun := kmswRevDart w wr n hrev
  invFun := kmswRevDart wr w n (kmswReversal_letters_symm wr w n hrev)
  left_inv := kmswRevDart_inverse w wr n hrev
  right_inv := kmswRevDart_inverse wr w n (kmswReversal_letters_symm wr w n hrev)




@[expose] def reversalDartVal {k : ℕ} (d : StageDart k) : ℕ × Bool :=
  (d.1.val, d.2)




private theorem reversalDartVal_injective (k : ℕ) :
    Function.Injective (reversalDartVal (k := k)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  obtain ⟨he, hb⟩ := Prod.mk.inj h
  exact Prod.ext (Fin.ext he) hb




@[expose] noncomputable def reversalDartValMap (w wr : ℕ → Fin 3) (n : ℕ)
    (d : ℕ × Bool) : ℕ × Bool := (kmswRevEdge w wr n d.1, !d.2)




private theorem reversal_triangle_active (w : ℕ → Fin 3) (s : ℕ)
    (hc : w s = 0 ∨ w s = 1) :
    (kmswStage w (s + 1)).active = (kmswStage w s).nextEdge := by
  rcases hc with hc | hc
  · simp only [kmswStage, kmswStep, kmswCodeStep, hc, ↓reduceIte]
    cases hl : (kmswStage w s).UL.dropLast.reverse <;>
      simp only [kmswStepOfStep, hl, State.addEdge]
  · simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]




private theorem reversal_up_pair_active (w : ℕ → Fin 3) {s t : ℕ}
    (hp : kmswRpair w s t) :
    (kmswStage w (t + 1)).active = (kmswStage w s).nextEdge + 1 := by
  have ht := (kmswRpair_codes w hp).2
  cases hh : (kmswStage w t).UR with
  | nil => exact ((kmswStage_down_head_nil_iff w t ht).mp hh ⟨s, hp⟩).elim
  | cons e es =>
    obtain ⟨s', hs', he⟩ := kmswStage_down_head_pair w t e es ht hh
    have hss : s' = s := kmswRpair_left_unique w hs' hp
    subst s'
    exact (kmswStage_down_UR_cons_endpoints w t e es ht hh).1.trans he




private theorem reversal_up_third (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (t : ℕ) (ht : t < n) (hc : wr t = 1) :
    kmswRevEdge w wr n ((kmswStage wr t).nextEdge + 1) =
      match (kmswStage w (n - 1 - t)).UL.dropLast.reverse with
      | [] => (kmswStage w (n - 1 - t)).nextEdge + 1
      | e :: _ => e := by
  have hr := kmswReversal_letters_symm wr w n hrev
  have hidx : n - 1 - (n - 1 - t) = t := by omega
  have hc' : w (n - 1 - t) = 0 := by
    rw [hr _ (by omega), hidx, hc]
    decide
  cases hl : (kmswStage w (n - 1 - t)).UL.dropLast.reverse with
  | nil =>
    have hlen := kmswStage_UL_length w (n - 1 - t)
    have hempty := congrArg List.length hl
    simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hempty
    have hbound := runningMin_le (L w) (n - 1 - t) (n - 1 - t) le_rfl
    change minL w (n - 1 - t) ≤ L w (n - 1 - t) at hbound
    have hmin : L w (n - 1 - t) = minL w (n - 1 - t) := by omega
    have hrec : kmswRevLeftRecord w n
        ((kmswStage w (n - 1 - t)).nextEdge + 1) (n - 1 - t) := by
      exact ⟨by omega, hc', hmin, rfl⟩
    have hu := kmswRevLeftRecord_reverse w wr n _ _ hr hrec
    rw [hidx] at hu
    rw [kmswRevEdge_up w wr n _ t hu]
  | cons e es =>
    obtain ⟨r, hp, he⟩ := kmswStage_left_head_pair w _ e es hc' hl
    have hp' : kmswRpair wr t (n - 1 - r) := by
      have hh := (kmswLpairBody_reverse_iff w wr n hr (by omega)).mp hp
      simpa only [hidx, kmswRpair] using hh
    have ha := reversal_up_pair_active wr hp'
    have hi : n - 1 - r + 1 = n - r := by have := hp.1; omega
    rw [hi] at ha
    rw [← ha, kmswRevEdge_active w wr n (n - r) (Nat.sub_le n r),
      Nat.sub_sub_self (by have := hp.1; omega)]
    exact he.symm




private theorem reversal_up_triangle (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (j : TriangleCreationTime wr) (hj : j.val < n) (hc : wr j.val = 1) :
    ∃ j' : TriangleCreationTime w, j'.val = n - 1 - j.val ∧
      List.IsRotated ((stageTriangleDartList wr j).map (reversalDartValMap w wr n))
        (stageTriangleDartList w j') := by
  have hr := kmswReversal_letters_symm wr w n hrev
  have hi : n - 1 - (n - 1 - j.val) = j.val := by omega
  have hc' : w (n - 1 - j.val) = 0 := by
    rw [hr _ (by omega), hi, hc]
    decide
  let j' : TriangleCreationTime w := ⟨n - 1 - j.val, Or.inl hc'⟩
  refine ⟨j', rfl, ?_⟩
  have ha := reversal_triangle_active wr j.val (Or.inr hc)
  have ha' := reversal_triangle_active w j'.val (Or.inl hc')
  have hnew : kmswRevEdge w wr n (kmswStage wr j.val).nextEdge =
      (kmswStage w j'.val).active := by
    rw [← ha, kmswRevEdge_active w wr n (j.val + 1) (by omega)]
    rw [show n - (j.val + 1) = j'.val by dsimp [j']; omega]
  have hold : kmswRevEdge w wr n (kmswStage wr j.val).active =
      (kmswStage w j'.val).nextEdge := by
    rw [kmswRevEdge_active w wr n j.val (by omega)]
    have hidx : n - j.val = j'.val + 1 := by dsimp [j']; omega
    rw [hidx, ha']
  have hthird := reversal_up_third w wr n hrev j.val hj hc
  change kmswRevEdge w wr n ((kmswStage wr j.val).nextEdge + 1) =
    (match (kmswStage w j'.val).UL.dropLast.reverse with
    | [] => (kmswStage w j'.val).nextEdge + 1 | e :: _ => e) at hthird
  dsimp only [stageTriangleDartList]
  rw [stageTriangleDartTriple_up wr j hc]
  simp only [List.map_cons, List.map_nil, reversalDartValMap,
    Bool.not_false, Bool.not_true, hold, hnew]
  cases hl : (kmswStage w j'.val).UL.dropLast.reverse with
  | nil =>
    rw [stageTriangleDartTriple_left_fresh w j' hc' hl]
    simp only [hl] at hthird
    rw [hthird]
    exact ⟨2, rfl⟩
  | cons e es =>
    rw [stageTriangleDartTriple_left_existing w j' hc' e es hl]
    simp only [hl] at hthird
    rw [hthird]
    exact ⟨1, rfl⟩




theorem kmswRevDart_triangle_words (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (j : TriangleCreationTime wr) (hj : j.val < n) :
    ∃ j' : TriangleCreationTime w, j'.val = n - 1 - j.val ∧
      List.IsRotated ((stageTriangleDartList wr j).map (reversalDartValMap w wr n))
        (stageTriangleDartList w j') := by
  rcases j.property with hc | hc
  · have hr := kmswReversal_letters_symm wr w n hrev
    have hi : n - 1 - (n - 1 - j.val) = j.val := by omega
    have hc' : w (n - 1 - j.val) = 1 := by
      rw [hr _ (by omega), hi, hc]
      decide
    let k : TriangleCreationTime w := ⟨n - 1 - j.val, Or.inr hc'⟩
    obtain ⟨k', hk', hh⟩ := reversal_up_triangle wr w n hr k (by dsimp [k]; omega) hc'
    have heq : k' = j := Subtype.ext (by dsimp [k] at hk'; omega)
    subst k'
    have hh' := hh.map (reversalDartValMap w wr n)
    have hinv : ((stageTriangleDartList w k).map (reversalDartValMap wr w n)).map
        (reversalDartValMap w wr n) = stageTriangleDartList w k := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (stageTriangleDartList w k)]
      apply List.map_congr_left
      intro d hd
      apply Prod.ext
      · exact kmswRevEdge_inverse w wr n hr d.1
          (stageTriangleDartList_lt w n k (by dsimp [k]; omega) d hd)
      · exact Bool.not_not d.2
    rw [hinv] at hh'
    exact ⟨k, rfl, hh'.symm⟩
  · exact reversal_up_triangle w wr n hrev j hj hc




private theorem reversal_outer_word (w : ℕ → Fin 3) (n : ℕ) :
    stageOuterWordVal w n =
      ((kmswStage w n).UL ++ (kmswStage w n).UR).map (fun e => (e, false)) ++
      ((kmswStage w n).LL ++ (kmswStage w n).LR).reverse.map (fun e => (e, true)) := by
  simp only [stageOuterWordVal_eq_runs, List.map_append, List.reverse_append,
    List.append_assoc]




theorem kmswRevDart_outer_word (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    List.IsRotated ((stageOuterWordVal wr n).map (reversalDartValMap w wr n))
      (stageOuterWordVal w n) := by
  have hu := congrArg (List.map (fun e : ℕ => (e, true)))
    (kmswRevEdge_upper_boundary wr w n hrev)
  have hl := congrArg (List.map (fun e : ℕ => (e, false)))
    (congrArg List.reverse (kmswRevEdge_lower_boundary wr w n hrev))
  simp only [← List.map_reverse, List.reverse_reverse] at hl
  rw [reversal_outer_word, reversal_outer_word, List.map_append]
  have hu' :
      (((kmswStage wr n).UL ++ (kmswStage wr n).UR).map (fun e => (e, false))).map
        (reversalDartValMap w wr n) =
      ((kmswStage w n).LL ++ (kmswStage w n).LR).reverse.map (fun e => (e, true)) := by
    simpa only [List.map_map, Function.comp_def, reversalDartValMap,
      Bool.not_false] using hu
  have hl' :
      (((kmswStage wr n).LL ++ (kmswStage wr n).LR).reverse.map
        (fun e => (e, true))).map (reversalDartValMap w wr n) =
      ((kmswStage w n).UL ++ (kmswStage w n).UR).map (fun e => (e, false)) := by
    simpa only [List.map_map, Function.comp_def, reversalDartValMap,
      Bool.not_true] using hl
  rw [hu', hl']
  exact List.isRotated_append




@[expose] def reversalTriangleWord (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n) :
    List (StageDart (kmswStage w n).nextEdge) :=
  [stageTriangleDart₁ w n j hj, stageTriangleDart₂ w n j hj,
    stageTriangleDart₃ w n j hj]




private theorem reversalTriangleWord_val (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n) :
    (reversalTriangleWord w n j hj).map reversalDartVal = stageTriangleDartList w j := by
  simp only [reversalTriangleWord, List.map_cons, List.map_nil, reversalDartVal,
    stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃, stageTriangleDartAt,
    stageTriangleDartList]




private theorem reversal_three_cycle_rule {D : Type*} [DecidableEq D]
    {f : Equiv.Perm D} {a b c : D} (h : FaceSucc3Cycle f a b c)
    (d : D) (hd : d ∈ ([a, b, c] : List D)) :
    f d = ([a, b, c] : List D).formPerm d := by
  rcases h with ⟨ha, hb, hc, hab, hbc, hca⟩
  have hnd : ([a, b, c] : List D).Nodup := by simp [hab, hbc, hca.symm]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with hd | hd | hd
  · rw [hd]
    exact ha.trans (List.formPerm_apply_lt_getElem _ hnd 0 (by simp)).symm
  · rw [hd]
    exact hb.trans (List.formPerm_apply_lt_getElem _ hnd 1 (by simp)).symm
  · rw [hd]
    have hp := List.formPerm_apply_getElem ([a, b, c] : List D) hnd 2 (by simp)
    have hp' : ([a, b, c] : List D).formPerm c = a := by
      simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMod,
        List.getElem_cons_succ, List.getElem_cons_zero] using hp
    exact hc.trans hp'.symm




theorem reversalTriangleWord_faceSucc (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (d : StageDart (kmswStage w n).nextEdge) (hd : d ∈ reversalTriangleWord w n j hj) :
    (kmswMap w n).faceSucc d = (reversalTriangleWord w n j hj).formPerm d :=
  reversal_three_cycle_rule (stageTriangle_isFace w j n hj) d hd




private theorem reversalTriangleWord_nodup (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n) :
    (reversalTriangleWord w n j hj).Nodup := by
  have h := stageTriangle_isFace w j n hj
  rcases h with ⟨_, _, _, hab, hbc, hca⟩
  simp [reversalTriangleWord, hab, hbc, hca.symm]




private theorem reversal_formPerm_map {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (l : List A) (hl : l.Nodup)
    (x : A) (hx : x ∈ l) : (l.map f).formPerm (f x) = f (l.formPerm x) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have himap : i < (l.map f).length := by simpa only [List.length_map] using hi
  have hmap : (l.map f)[i]'himap = f l[i] := by simp only [List.getElem_map]
  have hs := List.formPerm_apply_getElem (l.map f) (hl.map hf) i himap
  rw [hmap] at hs
  rw [List.formPerm_apply_getElem l hl i hi]
  simpa only [List.length_map, List.getElem_map] using hs




private theorem reversal_rotated_of_val {k : ℕ} (l l' : List (StageDart k))
    (h : List.IsRotated (l.map reversalDartVal) (l'.map reversalDartVal)) :
    List.IsRotated l l' := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  apply List.map_injective_iff.mpr (reversalDartVal_injective k)
  simpa only [List.map_rotate] using hm




private theorem reversal_word_conj {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : Equiv.Perm A) (g : Equiv.Perm B) (E : A ≃ B)
    (l : List A) (l' : List B) (hl : l.Nodup)
    (hf : ∀ x ∈ l, f x = l.formPerm x)
    (hg : ∀ y ∈ l', g y = l'.formPerm y)
    (hword : List.IsRotated (l.map E) l') (x : A) (hx : x ∈ l) :
    E (f x) = g (E x) := by
  have hx' : E x ∈ l' := hword.mem_iff.mp (List.mem_map.mpr ⟨x, hx, rfl⟩)
  rw [hf x hx, hg (E x) hx']
  rw [← reversal_formPerm_map E E.injective l hl x hx,
    List.formPerm_eq_of_isRotated (hl.map E.injective) hword]




private theorem reversal_outer_typed (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i))) :
    List.IsRotated ((stageOuterWord wr n).map (kmswRevDartEquiv w wr n hrev))
      (stageOuterWord w n) := by
  apply reversal_rotated_of_val
  change List.IsRotated
    (((stageOuterWord wr n).map (kmswRevDartEquiv w wr n hrev)).map reversalDartVal)
    (stageOuterWordVal w n)
  simpa only [List.map_map, Function.comp_def, stageOuterWordVal, kmswRevDartEquiv,
    Equiv.coe_fn_mk, kmswRevDart, reversalDartValMap, reversalDartVal] using
    kmswRevDart_outer_word w wr n hrev




private theorem reversal_triangle_typed (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (j : TriangleCreationTime wr) (hj : j.val < n)
    (j' : TriangleCreationTime w) (hj' : j'.val < n)
    (hword : List.IsRotated ((stageTriangleDartList wr j).map
      (reversalDartValMap w wr n)) (stageTriangleDartList w j')) :
    List.IsRotated ((reversalTriangleWord wr n j hj).map
      (kmswRevDartEquiv w wr n hrev)) (reversalTriangleWord w n j' hj') := by
  apply reversal_rotated_of_val
  have hv : ((reversalTriangleWord wr n j hj).map
      (kmswRevDartEquiv w wr n hrev)).map reversalDartVal =
      (stageTriangleDartList wr j).map (reversalDartValMap w wr n) := by
    rw [List.map_map]
    calc
      (reversalTriangleWord wr n j hj).map
          (reversalDartVal ∘ kmswRevDartEquiv w wr n hrev) =
        (reversalTriangleWord wr n j hj).map
          (reversalDartValMap w wr n ∘ reversalDartVal) := rfl
      _ = ((reversalTriangleWord wr n j hj).map reversalDartVal).map
          (reversalDartValMap w wr n) := (List.map_map).symm
      _ = _ := by rw [reversalTriangleWord_val]
  rw [hv, reversalTriangleWord_val]
  exact hword




theorem kmswRevDart_faceSucc (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (d : StageDart (kmswStage wr n).nextEdge) :
    kmswRevDart w wr n hrev ((kmswMap wr n).faceSucc d) =
      (kmswMap w n).faceSucc (kmswRevDart w wr n hrev d) := by
  rcases stage_dart_partition wr n d with hd | ⟨j, ⟨hj, hd⟩, _⟩
  · exact reversal_word_conj (kmswMap wr n).faceSucc (kmswMap w n).faceSucc
      (kmswRevDartEquiv w wr n hrev) (stageOuterWord wr n) (stageOuterWord w n)
      (stageOuterWord_nodup wr n) (stageOuterWord_faceSucc wr n)
      (stageOuterWord_faceSucc w n) (reversal_outer_typed w wr n hrev) d hd
  · obtain ⟨j', hj', hword⟩ := kmswRevDart_triangle_words w wr n hrev j hj
    have hj'n : j'.val < n := by omega
    have hd' : d ∈ reversalTriangleWord wr n j hj := by
      have hv : reversalDartVal d ∈
          (reversalTriangleWord wr n j hj).map reversalDartVal := by
        rw [reversalTriangleWord_val]
        exact hd
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hv
      have heq' : e = d := reversalDartVal_injective _ heq
      exact heq' ▸ he
    exact reversal_word_conj (kmswMap wr n).faceSucc (kmswMap w n).faceSucc
      (kmswRevDartEquiv w wr n hrev) (reversalTriangleWord wr n j hj)
      (reversalTriangleWord w n j' hj'n) (reversalTriangleWord_nodup wr n j hj)
      (reversalTriangleWord_faceSucc wr n j hj)
      (reversalTriangleWord_faceSucc w n j' hj'n)
      (reversal_triangle_typed w wr n hrev j hj j' hj'n hword) d hd' 




theorem kmswStage_rev_rot (w wr : ℕ → Fin 3) (n : ℕ)
    (hrev : ∀ i < n, wr i = Equiv.swap (0 : Fin 3) 1 (w (n - 1 - i)))
    (d : StageDart (kmswStage wr n).nextEdge) :
    stageRot w n (kmswRevDart w wr n hrev d) =
      kmswRevDart w wr n hrev (stageRot wr n d) := by
  have hsymm (x : StageDart (kmswStage wr n).nextEdge) :
      kmswRevDart w wr n hrev ((stageRot wr n).symm x) =
        (stageRot w n).symm (kmswRevDart w wr n hrev x) := by
    have hs := kmswRevDart_faceSucc w wr n hrev (edgeFlip _ x)
    change kmswRevDart w wr n hrev
        ((stageRot wr n).symm (edgeFlip _ (edgeFlip _ x))) =
      (stageRot w n).symm (edgeFlip _ (kmswRevDart w wr n hrev (edgeFlip _ x))) at hs
    rw [kmswRevDart_flip] at hs
    simpa [edgeFlip] using hs
  have hs := hsymm (stageRot wr n d)
  have hs' : (stageRot w n).symm
      (kmswRevDart w wr n hrev (stageRot wr n d)) = kmswRevDart w wr n hrev d := by
    simpa only [Equiv.symm_apply_apply] using hs.symm
  have h := congrArg (stageRot w n) hs'
  simpa only [Equiv.apply_symm_apply] using h.symm

end DirectedDistances.KMSW
