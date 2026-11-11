module

public import DirectedDistances.KMSW.StageOuterCycle
public import DirectedDistances.KMSW.StageTrianglePersistence

/-! Supporting lemmas for paper labels `def-kmsw`, `lem-kmsw-left` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The edge-ID and side list consisting of the outer word followed by every
triangle dart triple is duplicate-free (`def-kmsw`, -/
theorem stageFaceDartVal_nodup (w : ℕ → Fin 3) (n : ℕ) :
    (stageOuterWordVal w n ++
      (stageTriangleTimes w n).flatMap (stageTriangleDartList w)).Nodup := by
  simpa only [stageTriangleDartsVal] using stage_dart_partition_nodup w n

/-- Every allocated edge and either geometric side occurs in the outer word
or one of the creation-time triangle triples (`def-kmsw`, -/
theorem stageFaceDartVal_complete (w : ℕ → Fin 3) (n e : ℕ) (b : Bool)
    (he : e < (kmswStage w n).nextEdge) :
    (e, b) ∈ stageOuterWordVal w n ++
      (stageTriangleTimes w n).flatMap (stageTriangleDartList w) := by
  have hc := stage_dart_partition_count w n (e, b)
  have hc' : (stageOuterWordVal w n ++ stageTriangleDartsVal w n).count (e, b) = 1 := by
    simpa [he] using hc
  have hp : 0 < (stageOuterWordVal w n ++ stageTriangleDartsVal w n).count (e, b) := by
    rw [hc']
    decide
  simpa only [stageTriangleDartsVal] using List.count_pos_iff.mp hp

private def stageDartVal (k : ℕ) (d : StageDart k) : ℕ × Bool :=
  (d.1.val, d.2)

private theorem stageDartVal_injective (k : ℕ) :
    Function.Injective (stageDartVal k) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  simp only [stageDartVal, Prod.mk.injEq] at h
  rcases h with ⟨he, hb⟩
  cases Fin.ext he
  cases hb
  rfl

private theorem rotated_of_injective_map {α β : Type*} (f : α → β)
    (hf : Function.Injective f) {l l' : List α}
    (h : l.map f ~r l'.map f) : l ~r l' := by
  rcases h with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hmapinj : Function.Injective (fun l : List α => l.map f) :=
    List.map_injective_iff.mpr hf
  apply hmapinj
  simpa only [List.map_rotate] using hm

private theorem formPerm_apply_mem_eq_next {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (x : α) (hx : x ∈ l) :
    l.formPerm x = l.next x hx := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem _ hl, List.formPerm_apply_getElem _ hl]

private theorem formPerm_map_injective {α β : Type*} [DecidableEq α]
    [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (l : List α) (hl : l.Nodup) (x : α) (hx : x ∈ l) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  have hl' := hl.map hf
  have hmem : f x ∈ l.map f := List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [formPerm_apply_mem_eq_next (l.map f) hl' (f x) hmem,
    formPerm_apply_mem_eq_next l hl x hx]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have himap : i < (l.map f).length := by simpa using hi
  have hmap : (l.map f)[i]'himap = f l[i] := by simp
  have hnext := List.next_getElem (l.map f) hl' i himap
  have hnext' : (l.map f).next (f l[i]) hmem =
      (l.map f)[(i + 1) % (l.map f).length]'
        (Nat.mod_lt _ (i.zero_le.trans_lt himap)) := by
    simpa only [hmap] using hnext
  rw [hnext', List.next_getElem _ hl i hi]
  simp

private theorem faceSucc3Cycle_nodup {α : Type*} {f : Equiv.Perm α}
    {a b c : α} (h : FaceSucc3Cycle f a b c) : ([a, b, c] : List α).Nodup := by
  rcases h with ⟨_, _, _, hab, hbc, hca⟩
  simp [hab, hbc, hca.symm]

private theorem faceSucc3Cycle_eq_formPerm {α : Type*} [DecidableEq α]
    {f : Equiv.Perm α} {a b c : α} (h : FaceSucc3Cycle f a b c) :
    ∀ x ∈ ([a, b, c] : List α), f x = ([a, b, c] : List α).formPerm x := by
  rcases h with ⟨ha, hb, hc, hab, hbc, hca⟩
  have hnd : ([a, b, c] : List α).Nodup := by
    simp [hab, hbc, hca.symm]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hxa | hxb | hxc
  · rw [hxa]
    have hp := List.formPerm_apply_lt_getElem ([a, b, c] : List α) hnd 0 (by simp)
    exact ha.trans hp.symm
  · rw [hxb]
    have hp := List.formPerm_apply_lt_getElem ([a, b, c] : List α) hnd 1 (by simp)
    exact hb.trans hp.symm
  · rw [hxc]
    have hp := List.formPerm_apply_getElem ([a, b, c] : List α) hnd 2 (by simp)
    have hp' : ([a, b, c] : List α).formPerm c = a := by
      simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMod,
        List.getElem_cons_succ, List.getElem_cons_zero] using hp
    exact hc.trans hp'.symm

private theorem faceSucc3Cycle_conj {α β : Type*} [DecidableEq α]
    [DecidableEq β] {f : Equiv.Perm α} {g : Equiv.Perm β}
    (e : α ≃ β) {a b c : α} {a' b' c' : β}
    (hs : FaceSucc3Cycle f a b c) (ht : FaceSucc3Cycle g a' b' c')
    (hrot : ([e a, e b, e c] : List β) ~r [a', b', c']) :
    e (f a) = g (e a) ∧ e (f b) = g (e b) ∧ e (f c) = g (e c) := by
  have hnd : ([a, b, c] : List α).Nodup := faceSucc3Cycle_nodup hs
  have hnd' : ([e a, e b, e c] : List β).Nodup := hnd.map e.injective
  have hperm : ([e a, e b, e c] : List β).formPerm =
      ([a', b', c'] : List β).formPerm :=
    List.formPerm_eq_of_isRotated hnd' hrot
  have hmem_a : e a ∈ ([a', b', c'] : List β) :=
    (hrot.mem_iff).mp (by simp)
  have hmem_b : e b ∈ ([a', b', c'] : List β) :=
    (hrot.mem_iff).mp (by simp)
  have hmem_c : e c ∈ ([a', b', c'] : List β) :=
    (hrot.mem_iff).mp (by simp)
  have hsource := faceSucc3Cycle_eq_formPerm hs
  have htarget := faceSucc3Cycle_eq_formPerm ht
  refine ⟨?_, ?_, ?_⟩
  · calc
      e (f a) = e (([a, b, c] : List α).formPerm a) := congrArg e (hsource a (by simp))
      _ = ([e a, e b, e c] : List β).formPerm (e a) :=
        (formPerm_map_injective e e.injective [a, b, c] hnd a (by simp)).symm
      _ = ([a', b', c'] : List β).formPerm (e a) := by rw [hperm]
      _ = g (e a) := (htarget (e a) hmem_a).symm
  · calc
      e (f b) = e (([a, b, c] : List α).formPerm b) := congrArg e (hsource b (by simp))
      _ = ([e a, e b, e c] : List β).formPerm (e b) :=
        (formPerm_map_injective e e.injective [a, b, c] hnd b (by simp)).symm
      _ = ([a', b', c'] : List β).formPerm (e b) := by rw [hperm]
      _ = g (e b) := (htarget (e b) hmem_b).symm
  · calc
      e (f c) = e (([a, b, c] : List α).formPerm c) := congrArg e (hsource c (by simp))
      _ = ([e a, e b, e c] : List β).formPerm (e c) :=
        (formPerm_map_injective e e.injective [a, b, c] hnd c (by simp)).symm
      _ = ([a', b', c'] : List β).formPerm (e c) := by rw [hperm]
      _ = g (e c) := (htarget (e c) hmem_c).symm

private def stageTriangleDartsTyped (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n) :
    List (StageDart (kmswStage w n).nextEdge) :=
  [stageTriangleDart₁ w n j hj, stageTriangleDart₂ w n j hj,
    stageTriangleDart₃ w n j hj]

private theorem stageTriangleDartsTyped_val (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n) :
    (stageTriangleDartsTyped w n j hj).map (stageDartVal _) =
      stageTriangleDartList w j := by
  simp [stageTriangleDartsTyped, stageTriangleDartList, stageTriangleDart₁,
    stageTriangleDart₂, stageTriangleDart₃, stageTriangleDartAt, stageDartVal]

private theorem stageOuterWord_conj_faceSucc
    (w w' : ℕ → Fin 3) (n n' : ℕ)
    (φ : Fin (kmswStage w n).nextEdge ≃ Fin (kmswStage w' n').nextEdge)
    (φv : ℕ → ℕ) (hφv : ∀ e, (φ e).val = φv e.val)
    (houter : List.IsRotated
      ((stageOuterWordVal w n).map (fun p => (φv p.1, p.2)))
      (stageOuterWordVal w' n'))
    (d : StageDart (kmswStage w n).nextEdge) (hd : d ∈ stageOuterWord w n) :
    Equiv.prodCongr φ (Equiv.refl Bool) ((kmswMap w n).faceSucc d) =
      (kmswMap w' n').faceSucc (Equiv.prodCongr φ (Equiv.refl Bool) d) := by
  let Φ : StageDart (kmswStage w n).nextEdge ≃
      StageDart (kmswStage w' n').nextEdge := Equiv.prodCongr φ (Equiv.refl Bool)
  let v : StageDart (kmswStage w n).nextEdge → ℕ × Bool := stageDartVal _
  let v' : StageDart (kmswStage w' n').nextEdge → ℕ × Bool := stageDartVal _
  let g : ℕ × Bool → ℕ × Bool := fun p => (φv p.1, p.2)
  have hpoint : ∀ d, v' (Φ d) = g (v d) := by
    rintro ⟨e, b⟩
    simp [v, v', g, Φ, stageDartVal, hφv]
  have hmapval : ((stageOuterWord w n).map Φ).map v' =
      (stageOuterWordVal w n).map g := by
    rw [List.map_map]
    calc
      (stageOuterWord w n).map (v' ∘ Φ) = (stageOuterWord w n).map (g ∘ v) := by
        apply List.map_congr_left
        intro d _
        exact hpoint d
      _ = ((stageOuterWord w n).map v).map g := by rw [List.map_map]
      _ = (stageOuterWordVal w n).map g := by
        rw [stageOuterWordVal]
        rfl
  have htargetval : (stageOuterWord w' n').map v' = stageOuterWordVal w' n' := by
    simp [v', stageDartVal, stageOuterWordVal]
  have hrotval : ((stageOuterWord w n).map Φ).map v' ~r
      (stageOuterWord w' n').map v' := by
    rw [hmapval, htargetval]
    exact houter
  have hrot : (stageOuterWord w n).map Φ ~r stageOuterWord w' n' :=
    rotated_of_injective_map v' (stageDartVal_injective _) hrotval
  have hform : ((stageOuterWord w n).map Φ).formPerm =
      (stageOuterWord w' n').formPerm :=
    List.formPerm_eq_of_isRotated
      ((stageOuterWord_nodup w n).map Φ.injective) hrot
  have hmapform := formPerm_map_injective Φ Φ.injective
    (stageOuterWord w n) (stageOuterWord_nodup w n) d hd
  have hcycle := stageOuterWord_faceSucc w n d hd
  have htargetmem : Φ d ∈ stageOuterWord w' n' := by
    apply (hrot.mem_iff).mp
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  calc
    Φ ((kmswMap w n).faceSucc d) = Φ ((stageOuterWord w n).formPerm d) := by
      rw [hcycle]
    _ = ((stageOuterWord w n).map Φ).formPerm (Φ d) := hmapform.symm
    _ = (stageOuterWord w' n').formPerm (Φ d) := by
      exact congrArg (fun p : Equiv.Perm _ => p (Φ d)) hform
    _ = (kmswMap w' n').faceSucc (Φ d) :=
      (stageOuterWord_faceSucc w' n' (Φ d) htargetmem).symm

private theorem stageTriangle_conj_faceSucc
    (w w' : ℕ → Fin 3) (n n' : ℕ)
    (φ : Fin (kmswStage w n).nextEdge ≃ Fin (kmswStage w' n').nextEdge)
    (φv : ℕ → ℕ) (hφv : ∀ e, (φ e).val = φv e.val)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (j' : TriangleCreationTime w') (hj' : j'.val < n')
    (htri : List.IsRotated
      ((stageTriangleDartList w j).map (fun p => (φv p.1, p.2)))
      (stageTriangleDartList w' j'))
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : (d.1.val, d.2) ∈ stageTriangleDartList w j) :
    Equiv.prodCongr φ (Equiv.refl Bool) ((kmswMap w n).faceSucc d) =
      (kmswMap w' n').faceSucc (Equiv.prodCongr φ (Equiv.refl Bool) d) := by
  let Φ : StageDart (kmswStage w n).nextEdge ≃
      StageDart (kmswStage w' n').nextEdge := Equiv.prodCongr φ (Equiv.refl Bool)
  let v : StageDart (kmswStage w n).nextEdge → ℕ × Bool := stageDartVal _
  let v' : StageDart (kmswStage w' n').nextEdge → ℕ × Bool := stageDartVal _
  let g : ℕ × Bool → ℕ × Bool := fun p => (φv p.1, p.2)
  let s := stageTriangleDartsTyped w n j hj
  let t := stageTriangleDartsTyped w' n' j' hj'
  have hpoint : ∀ d, v' (Φ d) = g (v d) := by
    rintro ⟨e, b⟩
    simp [v, v', g, Φ, stageDartVal, hφv]
  have hmapval : (s.map Φ).map v' = (stageTriangleDartList w j).map g := by
    rw [List.map_map]
    calc
      s.map (v' ∘ Φ) = s.map (g ∘ v) := by
        apply List.map_congr_left
        intro d _
        exact hpoint d
      _ = (s.map v).map g := by rw [List.map_map]
      _ = (stageTriangleDartList w j).map g := by
        rw [← stageTriangleDartsTyped_val w n j hj]
  have htargetval : t.map v' = stageTriangleDartList w' j' := by
    simpa [t] using stageTriangleDartsTyped_val w' n' j' hj'
  have hrotval : (s.map Φ).map v' ~r t.map v' := by
    rw [hmapval, htargetval]
    exact htri
  have hrot : s.map Φ ~r t :=
    rotated_of_injective_map v' (stageDartVal_injective _) hrotval
  have hs : FaceSucc3Cycle (kmswMap w n).faceSucc
      (stageTriangleDart₁ w n j hj) (stageTriangleDart₂ w n j hj)
      (stageTriangleDart₃ w n j hj) := stageTriangle_isFace w j n hj
  have ht : FaceSucc3Cycle (kmswMap w' n').faceSucc
      (stageTriangleDart₁ w' n' j' hj') (stageTriangleDart₂ w' n' j' hj')
      (stageTriangleDart₃ w' n' j' hj') := stageTriangle_isFace w' j' n' hj'
  have hconj := faceSucc3Cycle_conj Φ hs ht hrot
  have h1 : v (stageTriangleDart₁ w n j hj) = (stageTriangleDartTriple w j).1 := by
    simp [v, stageDartVal, stageTriangleDart₁, stageTriangleDartAt]
  have h2 : v (stageTriangleDart₂ w n j hj) = (stageTriangleDartTriple w j).2.1 := by
    simp [v, stageDartVal, stageTriangleDart₂, stageTriangleDartAt]
  have h3 : v (stageTriangleDart₃ w n j hj) = (stageTriangleDartTriple w j).2.2 := by
    simp [v, stageDartVal, stageTriangleDart₃, stageTriangleDartAt]
  have hd' : v d = (stageTriangleDartTriple w j).1 ∨
      v d = (stageTriangleDartTriple w j).2.1 ∨
      v d = (stageTriangleDartTriple w j).2.2 := by
    simpa [v, stageDartVal, stageTriangleDartList] using hd
  rcases hd' with h | h | h
  · have heq : d = stageTriangleDart₁ w n j hj :=
      stageDartVal_injective _ (h.trans h1.symm)
    rw [heq]
    exact hconj.1
  · have heq : d = stageTriangleDart₂ w n j hj :=
      stageDartVal_injective _ (h.trans h2.symm)
    rw [heq]
    exact hconj.2.1
  · have heq : d = stageTriangleDart₃ w n j hj :=
      stageDartVal_injective _ (h.trans h3.symm)
    rw [heq]
    exact hconj.2.2




theorem kmswMap_conj_of_faces (w w' : ℕ → Fin 3) (n n' : ℕ)
    (φ : Fin (kmswStage w n).nextEdge ≃ Fin (kmswStage w' n').nextEdge)
    (φv : ℕ → ℕ) (hφv : ∀ e, (φ e).val = φv e.val)
    (houter : List.IsRotated
      ((stageOuterWordVal w n).map (fun p => (φv p.1, p.2)))
      (stageOuterWordVal w' n'))
    (htri : ∀ j : TriangleCreationTime w, j.val < n →
      ∃ j' : TriangleCreationTime w', j'.val < n' ∧
        List.IsRotated
          ((stageTriangleDartList w j).map (fun p => (φv p.1, p.2)))
          (stageTriangleDartList w' j')) :
    let Φ : StageDart (kmswStage w n).nextEdge ≃
        StageDart (kmswStage w' n').nextEdge := Equiv.prodCongr φ (Equiv.refl Bool)
    (∀ d, Φ ((kmswMap w n).faceSucc d) = (kmswMap w' n').faceSucc (Φ d)) ∧
      (∀ d, Φ ((kmswMap w n).rot d) = (kmswMap w' n').rot (Φ d)) ∧
      (∀ d, Φ (edgeFlip (kmswStage w n).nextEdge d) =
        edgeFlip (kmswStage w' n').nextEdge (Φ d)) := by
  let Φ : StageDart (kmswStage w n).nextEdge ≃
      StageDart (kmswStage w' n').nextEdge := Equiv.prodCongr φ (Equiv.refl Bool)
  have hface : ∀ d, Φ ((kmswMap w n).faceSucc d) =
      (kmswMap w' n').faceSucc (Φ d) := by
    intro d
    rcases stage_dart_partition w n d with hdOuter | hTriangle
    · exact stageOuterWord_conj_faceSucc w w' n n' φ φv hφv houter d hdOuter
    · obtain ⟨j, ⟨hj, hd⟩, _⟩ := hTriangle
      obtain ⟨j', hj', hrot⟩ := htri j hj
      exact stageTriangle_conj_faceSucc w w' n n' φ φv hφv j hj j' hj'
        hrot d hd
  have hedge : ∀ d, Φ (edgeFlip (kmswStage w n).nextEdge d) =
      edgeFlip (kmswStage w' n').nextEdge (Φ d) := by
    rintro ⟨e, b⟩
    cases b <;> rfl
  have hrot : ∀ d, Φ ((kmswMap w n).rot d) = (kmswMap w' n').rot (Φ d) := by
    intro d
    have hsymm : ∀ x, Φ ((kmswMap w n).rot.symm x) =
        (kmswMap w' n').rot.symm (Φ x) := by
      intro x
      have hs := hface (edgeFlip (kmswStage w n).nextEdge x)
      change Φ ((kmswMap w n).rot.symm
          (edgeFlip (kmswStage w n).nextEdge (edgeFlip (kmswStage w n).nextEdge x))) =
        (kmswMap w' n').rot.symm
          (edgeFlip (kmswStage w' n').nextEdge
            (Φ (edgeFlip (kmswStage w n).nextEdge x))) at hs
      rw [hedge x] at hs
      simpa [edgeFlip] using hs
    have hs := hsymm ((kmswMap w n).rot d)
    have hs' : (kmswMap w' n').rot.symm (Φ ((kmswMap w n).rot d)) = Φ d := by
      simpa using hs.symm
    have h := congrArg (kmswMap w' n').rot hs'
    simpa using h
  exact ⟨hface, hrot, hedge⟩

end DirectedDistances.KMSW
