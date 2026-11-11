module

public import DirectedDistances.KMSW.KMSWInverseProcedure

/-! # Predecessor data for inverse KMSW stages -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

private theorem dart_val_injective (k : ℕ) :
    Function.Injective (fun d : StageDart k => (d.1.val, d.2)) := by
  intro x y h
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (congrArg (fun d : ℕ × Bool => d.2) h)

private theorem formPerm_adjacent {D : Type*} [DecidableEq D]
    (p q : List D) (a b : D) (h : (p ++ a :: b :: q).Nodup) :
    (p ++ a :: b :: q).formPerm a = b := by
  have hlen : p.length + 1 < (p ++ a :: b :: q).length := by simp
  have ht := List.formPerm_apply_lt_getElem (p ++ a :: b :: q) h p.length hlen
  simpa using ht

/-- Consecutive west darts in the upper boundary satisfy the local rotation
identity. In particular this applies across the active/UR cut in -/
theorem stageRot_of_upper_adjacent (w : ℕ → Fin 3) (n : ℕ)
    (p q : List ℕ) (a b : Fin (kmswStage w n).nextEdge)
    (hab : (kmswStage w n).UL ++ (kmswStage w n).UR =
      p ++ a.val :: b.val :: q) :
    stageRot w n (b, false) = (a, true) := by
  let s := kmswStage w n
  have hp : ∀ e ∈ p, e < s.nextEdge := by
    intro e he
    have hm : e ∈ s.UL ++ s.UR := by rw [hab]; simp [he]
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at hm ⊢; tauto)
  have hq : ∀ e ∈ q, e < s.nextEdge := by
    intro e he
    have hm : e ∈ s.UL ++ s.UR := by rw [hab]; simp [he]
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append] at hm ⊢; tauto)
  let P := stageDarts s p false hp
  let Q := stageDarts s q false hq ++
    stageDarts s s.LR.reverse true (fun e he =>
      (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        simp only [List.mem_append]; exact Or.inr (List.mem_reverse.mp he))) ++
    stageDarts s s.LL.reverse true (fun e he =>
      (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        simp only [List.mem_append]; exact Or.inl (Or.inr (List.mem_reverse.mp he))))
  have hw : stageOuterWord w n = P ++ (a, false) :: (b, false) :: Q := by
    apply List.map_injective_iff.mpr (dart_val_injective _)
    change stageOuterWordVal w n = _
    rw [stageOuterWordVal_eq_runs]
    simp only [← List.map_append]
    rw [hab]
    simp only [List.map_append, List.map_cons]
    simp [P, Q, stageDarts, List.map_map, List.append_assoc, s]
  have hm : (a, false) ∈ stageOuterWord w n := by rw [hw]; simp
  have hf := stageOuterWord_faceSucc w n (a, false) hm
  rw [hw, formPerm_adjacent P Q _ _ (by rw [← hw]; exact stageOuterWord_nodup w n)] at hf
  change (stageRot w n).symm (edgeFlip _ (a, false)) = (b, false) at hf
  have hf := congrArg (stageRot w n) hf
  simpa only [Equiv.apply_symm_apply, edgeFlip_apply, Bool.not_false] using hf.symm

/-- Activation-down recovers the previous active dart by the same local -/
theorem kmswRootedStage_down_activation_previousActiveDart
    (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = e :: es) :
    (kmswRootedStage w (n + 1)).previousActiveDart 2 =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root := by
  let s := kmswStage w n
  have hURs : s.UR = e :: es := hUR
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge := by
    change (kmswStep s (w n)).nextEdge = _
    simp only [kmswStep, ht, kmswStepOfStep, hURs]
  have he : e < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
    simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr (by rw [hUR]; simp))))
  obtain ⟨p, hp⟩ := kmswStage_UL_last w n
  have hadj : (kmswStage w (n + 1)).UL ++ (kmswStage w (n + 1)).UR =
      p ++ s.active :: e :: es := by
    change (kmswStep s (w n)).UL ++ (kmswStep s (w n)).UR = _
    simp only [kmswStep, ht, kmswStepOfStep, hURs]
    rw [hp]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  let a : Fin (kmswStage w (n + 1)).nextEdge :=
    ⟨s.active, (act_lt_nextEdge w (le_refl n)).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_succ n))⟩
  let b : Fin (kmswStage w (n + 1)).nextEdge := ⟨e, by omega⟩
  have hr := stageRot_of_upper_adjacent w (n + 1) p es a b hadj
  have hroot : (kmswRootedStage w (n + 1)).root = (b, false) := by
    apply dart_val_injective
    change ((kmswStep s (w n)).active, false) = (e, false)
    simp only [kmswStep, ht, kmswStepOfStep, hURs]
  change edgeFlip _ (stageRot w (n + 1) (kmswRootedStage w (n + 1)).root) = _
  rw [hroot, hr]
  rfl

/-- Every down branch has the same intrinsic predecessor-root formula -/
theorem kmswRootedStage_down_previousActiveDart
    (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2) :
    (kmswRootedStage w (n + 1)).previousActiveDart 2 =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root := by
  cases hr : (kmswStage w n).UR with
  | nil => exact kmswRootedStage_down_pendant_previousActiveDart w n hc hr
  | cons e es => exact kmswRootedStage_down_activation_previousActiveDart w n e es hc hr

/-- The previous active dart is recovered intrinsically in every branch, -/
theorem kmswRootedStage_previousActiveDart (w : ℕ → Fin 3) (n : ℕ) :
    (kmswRootedStage w (n + 1)).previousActiveDart (w n) =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root := by
  by_cases h0 : w n = 0
  · rw [h0]; exact kmswRootedStage_left_previousActiveDart w n h0
  by_cases h1 : w n = 1
  · rw [h1]; exact kmswRootedStage_up_previousActiveDart w n h1
  have h2 : w n = 2 := by
    apply Fin.ext
    have hlt := (w n).isLt
    have hn0 : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
    have hn1 : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
    change (w n).val = 2
    omega
  rw [h2]; exact kmswRootedStage_down_previousActiveDart w n h2

/-- Successor-stage isomorphisms preserve the embedded predecessor root in -/
theorem RootedDirectedMapIso.predecessorRoot_comm
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) :
    h.dartEquiv
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
        (kmswRootedStage w n).root) =
      outerSucc_castDart (kmswStage_nextEdge_mono w' (Nat.le_succ n))
        (kmswRootedStage w' n).root := by
  rw [← kmswRootedStage_previousActiveDart, h.previousActiveDart_comm,
    lastCode_of_iso w w' n h, kmswRootedStage_previousActiveDart]

/-- The active dart belongs to the distinguished outer face -/
theorem kmswRootedStage_root_isOuter (w : ℕ → Fin 3) (n : ℕ) :
    (kmswRootedStage w n).map.IsOuter (kmswRootedStage w n).root := by
  obtain ⟨p, hp⟩ := kmswStage_UL_last w n
  have hm : (kmswStage w n).active ∈ (kmswStage w n).UL := by rw [hp]; simp
  exact ((kmswStageDirectedMap_UL_bridge w n
    ⟨(kmswStage w n).active, act_lt_nextEdge w (le_refl n)⟩).mp hm).2.2

private theorem sameCycle_transport {D E : Type*} [Finite D] [Finite E]
    (f : D ≃ E) (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (hc : ∀ d, f (σ d) = τ (f d)) (a b : D) :
    σ.SameCycle a b ↔ τ.SameCycle (f a) (f b) := by
  have hp : ∀ k : ℕ, ∀ d, f ((σ ^ k) d) = (τ ^ k) (f d) := by
    intro k d
    induction k with
    | zero => rfl
    | succ k ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hc] using congrArg τ ih
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, (hp k a).symm.trans (congrArg f hk)⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    exact ⟨k, f.injective ((hp k a).trans hk)⟩

private theorem outer_transport_of_root {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (M : RootedDirectedMapWithMissing D) (N : RootedDirectedMapWithMissing E)
    (f : D ≃ E) (hr : ∀ d, f (M.map.rot d) = N.map.rot (f d))
    (he : ∀ d, f (M.map.toCombinatorialMap.edgeInv d) =
      N.map.toCombinatorialMap.edgeInv (f d)) (hroot : f M.root = N.root)
    (hM : M.map.IsOuter M.root) (hN : N.map.IsOuter N.root) (d : D) :
    M.map.IsOuter d ↔ N.map.IsOuter (f d) := by
  have hface : ∀ x, f (M.map.toCombinatorialMap.faceSucc x) =
      N.map.toCombinatorialMap.faceSucc (f x) := by
    intro x
    apply N.map.rot.injective
    change N.map.rot (f (M.map.rot.symm (M.map.toCombinatorialMap.edgeInv x))) =
      N.map.rot (N.map.rot.symm (N.map.toCombinatorialMap.edgeInv (f x)))
    rw [← hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply, he]
  have ht := sameCycle_transport f M.map.toCombinatorialMap.faceSucc
    N.map.toCombinatorialMap.faceSucc hface M.root d
  rw [hroot] at ht
  change M.map.toCombinatorialMap.faceSucc.SameCycle M.map.outer d ↔
    N.map.toCombinatorialMap.faceSucc.SameCycle N.map.outer (f d)
  exact ⟨fun hd => hN.trans (ht.mp (hM.symm.trans hd)),
    fun hd => hM.trans (ht.mpr (hN.symm.trans hd))⟩

private def castDartEquiv {k l : ℕ} (h : k = l) : StageDart k ≃ StageDart l :=
  Equiv.prodCongr (finCongr h) (Equiv.refl Bool)

private theorem castDartEquiv_apply {k l : ℕ} (h : k = l) (d : StageDart k) :
    castDartEquiv h d = outerSucc_castDart (Nat.le_of_eq h) d := rfl

private theorem cast_resize_apply {k l : ℕ} (h : l = k)
    (σ : Equiv.Perm (StageDart k)) (τ : Equiv.Perm (StageDart l))
    (hh : StageRotation.resize h τ = σ) (d : StageDart k) :
    castDartEquiv h.symm (σ d) = τ (castDartEquiv h.symm d) := by
  subst l
  change τ = σ at hh
  rw [hh]
  rfl

private theorem activation_size (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = e :: es) :
    (kmswStage w n).nextEdge = (kmswStage w (n + 1)).nextEdge := by
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR]

private theorem activation_rot (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = e :: es)
    (d : StageDart (kmswStage w n).nextEdge) :
    castDartEquiv (activation_size w n e es hc hUR) (stageRot w n d) =
      stageRot w (n + 1) (castDartEquiv (activation_size w n e es hc hUR) d) := by
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have hh := StageRotation.step_activation (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) ht e es hUR
  change StageRotation.resize _ (stageRot w (n + 1)) = stageRot w n at hh
  exact cast_resize_apply (activation_size w n e es hc hUR).symm _ _ hh d

private def onRootEdge {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) (d : D) : Prop :=
  d = M.root ∨ d = M.map.toCombinatorialMap.edgeInv M.root

private theorem onRootEdge_comm {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (d : D) :
    onRootEdge M d ↔ onRootEdge N (h.dartEquiv d) := by
  have he : h.dartEquiv (M.map.toCombinatorialMap.edgeInv M.root) =
      N.map.toCombinatorialMap.edgeInv N.root := by rw [h.edgeFlip_comm, h.root_comm]
  unfold onRootEdge
  rw [← he, ← h.root_comm, h.dartEquiv.injective.eq_iff, h.dartEquiv.injective.eq_iff]

private theorem activation_rootEdge (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = e :: es)
    (d : StageDart (kmswStage w n).nextEdge) :
    onRootEdge (kmswRootedStage w (n + 1))
      (castDartEquiv (activation_size w n e es hc hUR) d) ↔ d.1.val = e := by
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have ha : (kmswStage w (n + 1)).active = e := by
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR]
  unfold onRootEdge
  change ((Fin.cast (activation_size w n e es hc hUR) d.1, d.2) = (⟨_, _⟩, false) ∨
    (Fin.cast (activation_size w n e es hc hUR) d.1, d.2) = (⟨_, _⟩, !false)) ↔ _
  simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_cast, ha, Bool.not_false]
  cases d.2 <;> simp

private theorem activation_missing (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = e :: es)
    (d : StageDart (kmswStage w n).nextEdge) :
    (kmswRootedStage w n).map.missing d ↔
      (kmswRootedStage w (n + 1)).map.missing
        (castDartEquiv (activation_size w n e es hc hUR) d) ∨
      onRootEdge (kmswRootedStage w (n + 1))
        (castDartEquiv (activation_size w n e es hc hUR) d) := by
  rw [activation_rootEdge w n e es hc hUR d]
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr (by rw [hUR]; simp))))
  have hm : (kmswStage w n).present e = false :=
    ((kmswStage_status w n).1 e he).mpr (Or.inl (by rw [hUR]; simp))
  change (kmswStage w n).present d.1.val = false ↔
    (kmswStage w (n + 1)).present d.1.val = false ∨ d.1.val = e
  simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR]
  by_cases hd : d.1.val = e
  · simp only [hd, ↓reduceIte, hm, Bool.true_eq_false, false_or]
  · simp only [hd, ↓reduceIte, or_false]

private theorem activation_tail (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = e :: es)
    (d : StageDart (kmswStage w n).nextEdge) :
    (kmswRootedStage w n).map.tail d ↔
      (kmswRootedStage w (n + 1)).map.tail
        (castDartEquiv (activation_size w n e es hc hUR) d) ∧
      ¬ onRootEdge (kmswRootedStage w (n + 1))
        (castDartEquiv (activation_size w n e es hc hUR) d) := by
  rw [activation_rootEdge w n e es hc hUR d]
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have he : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr (by rw [hUR]; simp))))
  have hm : (kmswStage w n).present e = false :=
    ((kmswStage_status w n).1 e he).mpr (Or.inl (by rw [hUR]; simp))
  change ((kmswStage w n).present d.1.val = true ∧ d.2 = false) ↔
    ((kmswStage w (n + 1)).present d.1.val = true ∧ d.2 = false) ∧ d.1.val ≠ e
  simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR]
  by_cases hd : d.1.val = e
  · simp [hd, hm]
  · simp [hd]

private theorem cast_edgeFlip {k l : ℕ} (h : k = l) (d : StageDart k) :
    castDartEquiv h (edgeFlip k d) = edgeFlip l (castDartEquiv h d) := rfl

/-- In the activation-down branch no darts are deleted. Restricting the
successor isomorphism consists of re-marking its root edge as missing and
moving the root back to the recovered active dart (`def-kmsw`, -/
def RootedDirectedMapIso.predecessor_activation
    (w w' : ℕ → Fin 3) (n e e' : ℕ) (es es' : List ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = e :: es)
    (hUR' : (kmswStage w' n).UR = e' :: es') :
    RootedDirectedMapIso (kmswRootedStage w n) (kmswRootedStage w' n) := by
  have hc' : w' n = 2 := (lastCode_of_iso w w' n h).symm.trans hc
  let E := castDartEquiv (activation_size w n e es hc hUR)
  let E' := castDartEquiv (activation_size w' n e' es' hc' hUR')
  let f := (E.trans h.dartEquiv).trans E'.symm
  have hf : ∀ d, E' (f d) = h.dartEquiv (E d) := by
    intro d
    exact E'.apply_symm_apply _
  have hr : ∀ d, f (stageRot w n d) = stageRot w' n (f d) := by
    intro d
    apply E'.injective
    have hh : ∀ x, h.dartEquiv (stageRot w (n + 1) x) =
      stageRot w' (n + 1) (h.dartEquiv x) := h.rot_comm
    rw [hf, activation_rot w n e es hc hUR, hh, ← hf,
      activation_rot w' n e' es' hc' hUR']
  have he : ∀ d, f (edgeFlip _ d) = edgeFlip _ (f d) := by
    intro d
    apply E'.injective
    have hh : ∀ x, h.dartEquiv (edgeFlip _ x) = edgeFlip _ (h.dartEquiv x) :=
      h.edgeFlip_comm
    rw [hf, cast_edgeFlip, hh, ← hf, cast_edgeFlip]
  have hroot : f (kmswRootedStage w n).root = (kmswRootedStage w' n).root := by
    apply E'.injective
    rw [hf]
    exact h.predecessorRoot_comm w w' n
  have hm : ∀ d, (kmswRootedStage w n).map.missing d ↔
      (kmswRootedStage w' n).map.missing (f d) := by
    intro d
    rw [activation_missing w n e es hc hUR,
      activation_missing w' n e' es' hc' hUR']
    change (_ ∨ onRootEdge _ (E d)) ↔ (_ ∨ onRootEdge _ (E' (f d)))
    rw [hf, ← h.missing_iff, ← onRootEdge_comm]
  have ht : ∀ d, (kmswRootedStage w n).map.tail d ↔
      (kmswRootedStage w' n).map.tail (f d) := by
    intro d
    rw [activation_tail w n e es hc hUR,
      activation_tail w' n e' es' hc' hUR']
    change (_ ∧ ¬ onRootEdge _ (E d)) ↔ (_ ∧ ¬ onRootEdge _ (E' (f d)))
    rw [hf, ← h.tail_iff, ← onRootEdge_comm]
  exact {
    dartEquiv := f
    rot_comm := hr
    edgeFlip_comm := he
    missing_iff := hm
    present_iff := fun d => not_congr (hm d)
    tail_iff := ht
    outer_iff := outer_transport_of_root _ _ f hr he hroot
      (kmswRootedStage_root_isOuter w n) (kmswRootedStage_root_isOuter w' n)
    root_comm := hroot }

private theorem rot_eq_of_resize {k l : ℕ} (hs : k = l)
    (R : Equiv.Perm (StageDart k)) (σ : Equiv.Perm (StageDart l))
    (hR : StageRotation.resize hs R = σ)
    (x y : StageDart k) (x' y' : StageDart l)
    (hx : (x.1.val, x.2) = (x'.1.val, x'.2))
    (hy : (y.1.val, y.2) = (y'.1.val, y'.2)) (ht : σ x' = y') : R x = y := by
  subst hs
  have hx' := dart_val_injective _ hx
  have hy' := dart_val_injective _ hy
  change R = σ at hR
  rw [hR, hx', hy']
  exact ht

/-- The two created up-step edges are selected intrinsically by the root -/
theorem kmswRootedStage_up_head_rotation (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1) :
    (stageRot w (n + 1) (edgeFlip _ (kmswRootedStage w (n + 1)).root)).1.val =
      (kmswStage w n).nextEdge + 1 ∧
    (stageRot w (n + 1) (edgeFlip _ (kmswRootedStage w (n + 1)).root)).2 = false := by
  let s := kmswStage w n
  have ht : kmswCodeStep (w n) = .up := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 2 := by
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, State.addEdge]
    rfl
  let d : StageDart (kmswStage w (n + 1)).nextEdge :=
    (⟨s.nextEdge + 1, by omega⟩, false)
  have hr := StageRotation.step_up s (act_lt_nextEdge w (le_refl n))
    (stageRotation_UL_bound w n) (stageRot w n) (w n) ht
  have hn := (StageRotation.up_new s.nextEdge (stageRot w n)
    (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, false)
    (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true)).2.2.1
  have hd : stageRot w (n + 1)
      (edgeFlip _ (kmswRootedStage w (n + 1)).root) = d := by
    apply rot_eq_of_resize hs _ _ hr _ d _ _ ?_ ?_ hn
    · simp only [edgeFlip, kmswRootedStage, kmswStage, kmswStep, ht,
        kmswStepOfStep, State.addEdge, StageRotation.allocation]
      rfl
    · rfl
  rw [hd]
  exact ⟨rfl, rfl⟩

private def upCreated {D : Type*} [Fintype D] [DecidableEq D]
    (M : RootedDirectedMapWithMissing D) (d : D) : Prop :=
  onRootEdge M d ∨ d = M.map.rot (M.map.toCombinatorialMap.edgeInv M.root) ∨
    d = M.map.toCombinatorialMap.edgeInv
      (M.map.rot (M.map.toCombinatorialMap.edgeInv M.root))

private theorem upCreated_comm {D E : Type*}
    [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (h : RootedDirectedMapIso M N) (d : D) :
    upCreated M d ↔ upCreated N (h.dartEquiv d) := by
  have hs : h.dartEquiv (M.map.rot (M.map.toCombinatorialMap.edgeInv M.root)) =
      N.map.rot (N.map.toCombinatorialMap.edgeInv N.root) := by
    rw [h.rot_comm, h.edgeFlip_comm, h.root_comm]
  have ht : h.dartEquiv (M.map.toCombinatorialMap.edgeInv
      (M.map.rot (M.map.toCombinatorialMap.edgeInv M.root))) =
      N.map.toCombinatorialMap.edgeInv
        (N.map.rot (N.map.toCombinatorialMap.edgeInv N.root)) := by
    rw [h.edgeFlip_comm, hs]
  unfold upCreated
  rw [← onRootEdge_comm h, ← ht, ← hs,
    h.dartEquiv.injective.eq_iff, h.dartEquiv.injective.eq_iff]

private theorem sameEdge_darts {k : ℕ} (d a : StageDart k) :
    (d = a ∨ d = edgeFlip k a) ↔ d.1.val = a.1.val := by
  rcases d with ⟨d, b⟩
  rcases a with ⟨a, c⟩
  simp only [edgeFlip_apply, Prod.mk.injEq, Fin.ext_iff]
  cases b <;> cases c <;> simp

private theorem upCreated_iff (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    upCreated (kmswRootedStage w (n + 1)) d ↔
      (kmswStage w n).nextEdge ≤ d.1.val := by
  have ht : kmswCodeStep (w n) = .up := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 := by
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, State.addEdge]
  have ha : (kmswRootedStage w (n + 1)).root.1.val = (kmswStage w n).nextEdge := by
    simp only [kmswRootedStage, kmswStage, kmswStep, ht, kmswStepOfStep, State.addEdge]
  have hb := (kmswRootedStage_up_head_rotation w n hc).1
  unfold upCreated onRootEdge
  change (d = _ ∨ d = edgeFlip _ _) ∨ d = _ ∨ d = edgeFlip _ _ ↔ _
  rw [sameEdge_darts, sameEdge_darts, ha]
  change (d.1.val = _ ∨ d.1.val =
    (stageRot w (n + 1) (edgeFlip _ (kmswRootedStage w (n + 1)).root)).1.val) ↔ _
  rw [hb]
  have hd := d.1.isLt
  omega

/-- A successor isomorphism sends precisely the old darts to old darts in -/
theorem RootedDirectedMapIso.up_surviving_iff
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 1)
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    d.1.val < (kmswStage w n).nextEdge ↔
      (h.dartEquiv d).1.val < (kmswStage w' n).nextEdge := by
  have hc' : w' n = 1 := (lastCode_of_iso w w' n h).symm.trans hc
  have ht := upCreated_comm h d
  rw [upCreated_iff w n hc, upCreated_iff w' n hc'] at ht
  omega

/-- Old darts identified with their surviving images under allocation -/
@[expose] def survivingDartEquiv {k l : ℕ} (h : k ≤ l) :
    StageDart k ≃ {d : StageDart l // d.1.val < k} where
  toFun d := ⟨outerSucc_castDart h d, d.1.isLt⟩
  invFun d := (⟨d.1.1.val, d.2⟩, d.1.2)
  left_inv d := rfl
  right_inv d := by
    apply Subtype.ext
    rfl

/-- The successor dart equivalence restricted to surviving darts of an up
transport are separate obligations. -/
@[expose] def RootedDirectedMapIso.predecessorDartEquiv_up
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 1) :
    StageDart (kmswStage w n).nextEdge ≃ StageDart (kmswStage w' n).nextEdge :=
  ((survivingDartEquiv (kmswStage_nextEdge_mono w (Nat.le_succ n))).trans
    (h.dartEquiv.subtypeEquiv (h.up_surviving_iff w w' n hc))).trans
    (survivingDartEquiv (kmswStage_nextEdge_mono w' (Nat.le_succ n))).symm

/-- The restricted up-step equivalence agrees with the original
isomorphism after embedding old darts (`def-kmsw`, -/
theorem RootedDirectedMapIso.predecessorDartEquiv_up_comm
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 1)
    (d : StageDart (kmswStage w n).nextEdge) :
    outerSucc_castDart (kmswStage_nextEdge_mono w' (Nat.le_succ n))
      (h.predecessorDartEquiv_up w w' n hc d) =
      h.dartEquiv (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) := rfl

private def skipTwo {D : Type*} (σ : D → D) (p : D → Prop) [DecidablePred p]
    (d : D) : D :=
  if p (σ d) then σ d else if p (σ (σ d)) then σ (σ d) else σ (σ (σ d))

private theorem up_skip (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (a A d : StageDart k) :
    StageRotation.allocation k 2 (.inl (σ d)) =
      skipTwo (StageRotation.up k σ a A) (fun x => x.1.val < k)
        (StageRotation.allocation k 2 (.inl d)) := by
  have hn := StageRotation.up_new k σ a A
  have hold : ∀ x : StageDart k,
      (StageRotation.allocation k 2 (.inl x)).1.val < k := fun x => x.1.isLt
  have hx : ¬ (StageRotation.allocation k 2 (.inr (0, false))).1.val < k := by
    change ¬ k + 0 < k; omega
  have hy : ¬ (StageRotation.allocation k 2 (.inr (1, true))).1.val < k := by
    change ¬ k + 1 < k; omega
  by_cases hda : d = a
  · subst d
    by_cases hA : σ a = A
    · simp only [skipTwo, StageRotation.up_old, ↓reduceIte, hx, hn.1, hA,
        hy, hn.2.1]
    · simp only [skipTwo, StageRotation.up_old, ↓reduceIte, hx, hn.1, hA,
        hold]
  · by_cases hA : σ d = A
    · simp only [skipTwo, StageRotation.up_old, hda, hA, ↓reduceIte, hy,
        hn.2.1, hold]
    · simp only [skipTwo, StageRotation.up_old, hda, hA, ↓reduceIte, hold]

private theorem up_skip_resize {k l : ℕ} (hs : l = k + 2)
    (σ : Equiv.Perm (StageDart k)) (R : Equiv.Perm (StageDart l))
    (a A d : StageDart k)
    (hR : StageRotation.resize hs R = StageRotation.up k σ a A) :
    castDartEquiv hs.symm (StageRotation.allocation k 2 (.inl (σ d))) =
      skipTwo R (fun x => x.1.val < k)
        (castDartEquiv hs.symm (StageRotation.allocation k 2 (.inl d))) := by
  subst l
  change R = StageRotation.up k σ a A at hR
  rw [hR]
  exact up_skip k σ a A d

private theorem stage_up_skip (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (d : StageDart (kmswStage w n).nextEdge) :
    outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) (stageRot w n d) =
      skipTwo (stageRot w (n + 1)) (fun x => x.1.val < (kmswStage w n).nextEdge)
        (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) := by
  have ht : kmswCodeStep (w n) = .up := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 2 := by
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, State.addEdge]
  have hr := StageRotation.step_up (kmswStage w n) (act_lt_nextEdge w (le_refl n))
    (stageRotation_UL_bound w n) (stageRot w n) (w n) ht
  exact up_skip_resize hs (stageRot w n) (stageRot w (n + 1)) _ _ d hr

private theorem skipTwo_comm {D E : Type*} (f : D → E) (σ : D → D) (τ : E → E)
    (p : D → Prop) (q : E → Prop) [DecidablePred p] [DecidablePred q]
    (hr : ∀ d, f (σ d) = τ (f d)) (hp : ∀ d, p d ↔ q (f d)) (d : D) :
    f (skipTwo σ p d) = skipTwo τ q (f d) := by
  simp only [skipTwo, ← hr, ← hp]
  split_ifs <;> rfl

private theorem castDart_injective {k l : ℕ} (h : k ≤ l) :
    Function.Injective (outerSucc_castDart h) := by
  intro d e he
  apply dart_val_injective k
  exact congrArg (fun d : StageDart l => (d.1.val, d.2)) he

/-- Rotation commutes with the restricted dart equivalence after the
created up-step darts are bypassed (`def-kmsw`, -/
theorem RootedDirectedMapIso.predecessorDartEquiv_up_rot
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 1)
    (d : StageDart (kmswStage w n).nextEdge) :
    h.predecessorDartEquiv_up w w' n hc (stageRot w n d) =
      stageRot w' n (h.predecessorDartEquiv_up w w' n hc d) := by
  have hc' : w' n = 1 := (lastCode_of_iso w w' n h).symm.trans hc
  apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
  rw [h.predecessorDartEquiv_up_comm w w' n hc, stage_up_skip w n hc,
    stage_up_skip w' n hc']
  have hr : ∀ x, h.dartEquiv (stageRot w (n + 1) x) =
      stageRot w' (n + 1) (h.dartEquiv x) := h.rot_comm
  rw [skipTwo_comm h.dartEquiv _ _
      (fun x => x.1.val < (kmswStage w n).nextEdge)
      (fun x => x.1.val < (kmswStage w' n).nextEdge) hr (h.up_surviving_iff w w' n hc),
    h.predecessorDartEquiv_up_comm w w' n hc]

private theorem stage_up_present (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1)
    (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    (kmswStage w (n + 1)).present e = (kmswStage w n).present e := by
  have ht : kmswCodeStep (w n) = .up := by rw [hc]; rfl
  have h0 : e ≠ (kmswStage w n).nextEdge := by omega
  have h1 : e ≠ (kmswStage w n).nextEdge + 1 := by omega
  simp only [kmswStage, kmswStep, ht, kmswStepOfStep, State.addEdge,
    h0, h1, ↓reduceIte]

private theorem castLE_edgeFlip {k l : ℕ} (h : k ≤ l) (d : StageDart k) :
    outerSucc_castDart h (edgeFlip k d) = edgeFlip l (outerSucc_castDart h d) := rfl

/-- Up-step predecessor isomorphism obtained by deleting exactly the two
created edges and bypassing their darts in vertex rotations -/
def RootedDirectedMapIso.predecessor_up
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 1) :
    RootedDirectedMapIso (kmswRootedStage w n) (kmswRootedStage w' n) := by
  have hc' : w' n = 1 := (lastCode_of_iso w w' n h).symm.trans hc
  let f := h.predecessorDartEquiv_up w w' n hc
  let E := outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
  let E' := outerSucc_castDart (kmswStage_nextEdge_mono w' (Nat.le_succ n))
  have hf : ∀ d, E' (f d) = h.dartEquiv (E d) :=
    h.predecessorDartEquiv_up_comm w w' n hc
  dsimp only [E, E'] at hf
  have hr : ∀ d, f (stageRot w n d) = stageRot w' n (f d) :=
    h.predecessorDartEquiv_up_rot w w' n hc
  have he : ∀ d, f (edgeFlip _ d) = edgeFlip _ (f d) := by
    intro d
    apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
    have hh : ∀ x, h.dartEquiv (edgeFlip _ x) = edgeFlip _ (h.dartEquiv x) :=
      h.edgeFlip_comm
    rw [hf, castLE_edgeFlip, hh, ← hf, castLE_edgeFlip]
  have hroot : f (kmswRootedStage w n).root = (kmswRootedStage w' n).root := by
    apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
    rw [hf]
    exact h.predecessorRoot_comm w w' n
  have hm : ∀ d, (kmswRootedStage w n).map.missing d ↔
      (kmswRootedStage w' n).map.missing (f d) := by
    intro d
    have hh := h.missing_iff (E d)
    rw [← hf] at hh
    change (kmswStage w (n + 1)).present d.1.val = false ↔
      (kmswStage w' (n + 1)).present (f d).1.val = false at hh
    rw [stage_up_present w n hc _ d.1.isLt,
      stage_up_present w' n hc' _ (f d).1.isLt] at hh
    exact hh
  have ht : ∀ d, (kmswRootedStage w n).map.tail d ↔
      (kmswRootedStage w' n).map.tail (f d) := by
    intro d
    have hh := h.tail_iff (E d)
    rw [← hf] at hh
    change ((kmswStage w (n + 1)).present d.1.val = true ∧ d.2 = false) ↔
      ((kmswStage w' (n + 1)).present (f d).1.val = true ∧ (f d).2 = false) at hh
    rw [stage_up_present w n hc _ d.1.isLt,
      stage_up_present w' n hc' _ (f d).1.isLt] at hh
    exact hh
  exact {
    dartEquiv := f
    rot_comm := hr
    edgeFlip_comm := he
    missing_iff := hm
    present_iff := fun d => not_congr (hm d)
    tail_iff := ht
    outer_iff := outer_transport_of_root _ _ f hr he hroot
      (kmswRootedStage_root_isOuter w n) (kmswRootedStage_root_isOuter w' n)
    root_comm := hroot }

private theorem pendant_created_iff (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = [])
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    onRootEdge (kmswRootedStage w (n + 1)) d ↔
      (kmswStage w n).nextEdge ≤ d.1.val := by
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 := by
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR, State.addEdge]
  have ha : (kmswRootedStage w (n + 1)).root.1.val = (kmswStage w n).nextEdge := by
    simp only [kmswRootedStage, kmswStage, kmswStep, ht, kmswStepOfStep, hUR,
      State.addEdge]
  unfold onRootEdge
  change (d = _ ∨ d = edgeFlip _ _) ↔ _
  rw [sameEdge_darts, ha]
  have hd := d.1.isLt
  omega

/-- In two pendant-down branches, a successor isomorphism preserves the -/
theorem RootedDirectedMapIso.pendant_surviving_iff
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) (hUR' : (kmswStage w' n).UR = [])
    (d : StageDart (kmswStage w (n + 1)).nextEdge) :
    d.1.val < (kmswStage w n).nextEdge ↔
      (h.dartEquiv d).1.val < (kmswStage w' n).nextEdge := by
  have hc' : w' n = 2 := (lastCode_of_iso w w' n h).symm.trans hc
  have hh := onRootEdge_comm h d
  rw [pendant_created_iff w n hc hUR, pendant_created_iff w' n hc' hUR'] at hh
  omega

/-- Restriction of the dart equivalence in two pendant-down branches -/
@[expose] def RootedDirectedMapIso.predecessorDartEquiv_pendant
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) (hUR' : (kmswStage w' n).UR = []) :
    StageDart (kmswStage w n).nextEdge ≃ StageDart (kmswStage w' n).nextEdge :=
  ((survivingDartEquiv (kmswStage_nextEdge_mono w (Nat.le_succ n))).trans
    (h.dartEquiv.subtypeEquiv (h.pendant_surviving_iff w w' n hc hUR hUR'))).trans
    (survivingDartEquiv (kmswStage_nextEdge_mono w' (Nat.le_succ n))).symm

/-- The pendant restriction agrees with the successor equivalence on old -/
theorem RootedDirectedMapIso.predecessorDartEquiv_pendant_comm
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) (hUR' : (kmswStage w' n).UR = [])
    (d : StageDart (kmswStage w n).nextEdge) :
    outerSucc_castDart (kmswStage_nextEdge_mono w' (Nat.le_succ n))
      (h.predecessorDartEquiv_pendant w w' n hc hUR hUR' d) =
      h.dartEquiv (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) := rfl

private theorem pendant_skip (k : ℕ) (σ : Equiv.Perm (StageDart k))
    (A d : StageDart k) :
    StageRotation.allocation k 1 (.inl (σ d)) =
      skipTwo (StageRotation.pendant k σ A) (fun x => x.1.val < k)
        (StageRotation.allocation k 1 (.inl d)) := by
  have hn := StageRotation.pendant_new k σ A
  have hold : ∀ x : StageDart k,
      (StageRotation.allocation k 1 (.inl x)).1.val < k := fun x => x.1.isLt
  have hx : ¬ (StageRotation.allocation k 1 (.inr (0, false))).1.val < k := by
    change ¬ k + 0 < k; omega
  by_cases hA : σ d = A
  · simp only [skipTwo, StageRotation.pendant_old, hA, ↓reduceIte, hx, hn.1, hold]
  · simp only [skipTwo, StageRotation.pendant_old, hA, ↓reduceIte, hold]

private theorem pendant_skip_resize {k l : ℕ} (hs : l = k + 1)
    (σ : Equiv.Perm (StageDart k)) (R : Equiv.Perm (StageDart l))
    (A d : StageDart k)
    (hR : StageRotation.resize hs R = StageRotation.pendant k σ A) :
    castDartEquiv hs.symm (StageRotation.allocation k 1 (.inl (σ d))) =
      skipTwo R (fun x => x.1.val < k)
        (castDartEquiv hs.symm (StageRotation.allocation k 1 (.inl d))) := by
  subst l
  change R = StageRotation.pendant k σ A at hR
  rw [hR]
  exact pendant_skip k σ A d

private theorem stage_pendant_skip (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) (d : StageDart (kmswStage w n).nextEdge) :
    outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) (stageRot w n d) =
      skipTwo (stageRot w (n + 1)) (fun x => x.1.val < (kmswStage w n).nextEdge)
        (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n)) d) := by
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge + 1 := by
    simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR, State.addEdge]
  have hr := StageRotation.step_pendant (kmswStage w n) (act_lt_nextEdge w (le_refl n))
    (stageRotation_UL_bound w n) (stageRot w n) (w n) ht hUR
  exact pendant_skip_resize hs (stageRot w n) (stageRot w (n + 1)) _ d hr

/-- Rotation transport after deletion of the pendant-down edge -/
theorem RootedDirectedMapIso.predecessorDartEquiv_pendant_rot
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) (hUR' : (kmswStage w' n).UR = [])
    (d : StageDart (kmswStage w n).nextEdge) :
    h.predecessorDartEquiv_pendant w w' n hc hUR hUR' (stageRot w n d) =
      stageRot w' n (h.predecessorDartEquiv_pendant w w' n hc hUR hUR' d) := by
  have hc' : w' n = 2 := (lastCode_of_iso w w' n h).symm.trans hc
  apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
  rw [h.predecessorDartEquiv_pendant_comm w w' n hc hUR hUR',
    stage_pendant_skip w n hc hUR, stage_pendant_skip w' n hc' hUR']
  have hr : ∀ x, h.dartEquiv (stageRot w (n + 1) x) =
      stageRot w' (n + 1) (h.dartEquiv x) := h.rot_comm
  rw [skipTwo_comm h.dartEquiv _ _
      (fun x => x.1.val < (kmswStage w n).nextEdge)
      (fun x => x.1.val < (kmswStage w' n).nextEdge) hr
      (h.pendant_surviving_iff w w' n hc hUR hUR'),
    h.predecessorDartEquiv_pendant_comm w w' n hc hUR hUR']

private theorem stage_pendant_present (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = [])
    (e : ℕ) (he : e < (kmswStage w n).nextEdge) :
    (kmswStage w (n + 1)).present e = (kmswStage w n).present e := by
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have h0 : e ≠ (kmswStage w n).nextEdge := by omega
  simp only [kmswStage, kmswStep, ht, kmswStepOfStep, hUR, State.addEdge,
    h0, ↓reduceIte]

/-- Pendant-down predecessor isomorphism, deleting the created edge -/
def RootedDirectedMapIso.predecessor_pendant
    (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (n + 1))
      (kmswRootedStage w' (n + 1))) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) (hUR' : (kmswStage w' n).UR = []) :
    RootedDirectedMapIso (kmswRootedStage w n) (kmswRootedStage w' n) := by
  have hc' : w' n = 2 := (lastCode_of_iso w w' n h).symm.trans hc
  let f := h.predecessorDartEquiv_pendant w w' n hc hUR hUR'
  let E := outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ n))
  let E' := outerSucc_castDart (kmswStage_nextEdge_mono w' (Nat.le_succ n))
  have hf : ∀ d, E' (f d) = h.dartEquiv (E d) :=
    h.predecessorDartEquiv_pendant_comm w w' n hc hUR hUR'
  dsimp only [E, E'] at hf
  have hr : ∀ d, f (stageRot w n d) = stageRot w' n (f d) :=
    h.predecessorDartEquiv_pendant_rot w w' n hc hUR hUR'
  have he : ∀ d, f (edgeFlip _ d) = edgeFlip _ (f d) := by
    intro d
    apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
    have hh : ∀ x, h.dartEquiv (edgeFlip _ x) = edgeFlip _ (h.dartEquiv x) :=
      h.edgeFlip_comm
    rw [hf, castLE_edgeFlip, hh, ← hf, castLE_edgeFlip]
  have hroot : f (kmswRootedStage w n).root = (kmswRootedStage w' n).root := by
    apply castDart_injective (kmswStage_nextEdge_mono w' (Nat.le_succ n))
    rw [hf]
    exact h.predecessorRoot_comm w w' n
  have hm : ∀ d, (kmswRootedStage w n).map.missing d ↔
      (kmswRootedStage w' n).map.missing (f d) := by
    intro d
    have hh := h.missing_iff (E d)
    rw [← hf] at hh
    change (kmswStage w (n + 1)).present d.1.val = false ↔
      (kmswStage w' (n + 1)).present (f d).1.val = false at hh
    rw [stage_pendant_present w n hc hUR _ d.1.isLt,
      stage_pendant_present w' n hc' hUR' _ (f d).1.isLt] at hh
    exact hh
  have ht : ∀ d, (kmswRootedStage w n).map.tail d ↔
      (kmswRootedStage w' n).map.tail (f d) := by
    intro d
    have hh := h.tail_iff (E d)
    rw [← hf] at hh
    change ((kmswStage w (n + 1)).present d.1.val = true ∧ d.2 = false) ↔
      ((kmswStage w' (n + 1)).present (f d).1.val = true ∧ (f d).2 = false) at hh
    rw [stage_pendant_present w n hc hUR _ d.1.isLt,
      stage_pendant_present w' n hc' hUR' _ (f d).1.isLt] at hh
    exact hh
  exact {
    dartEquiv := f
    rot_comm := hr
    edgeFlip_comm := he
    missing_iff := hm
    present_iff := fun d => not_congr (hm d)
    tail_iff := ht
    outer_iff := outer_transport_of_root _ _ f hr he hroot
      (kmswRootedStage_root_isOuter w n) (kmswRootedStage_root_isOuter w' n)
    root_comm := hroot }

/-- Successive up-step peeling recovers an arbitrary earlier letter through
partial inverse induction, not unrestricted prefix injectivity. -/
theorem code_of_iso_of_up_suffix (w w' : ℕ → Fin 3) (m k : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w (m + k + 1))
      (kmswRootedStage w' (m + k + 1)))
    (hup : ∀ j, m < j → j < m + k + 1 → w j = 1) : w m = w' m := by
  induction k with
  | zero => exact lastCode_of_iso w w' m h
  | succ k ih =>
    have hc : w (m + k + 1) = 1 := hup _ (by omega) (by omega)
    have hh : RootedDirectedMapIso (kmswRootedStage w ((m + k + 1) + 1))
        (kmswRootedStage w' ((m + k + 1) + 1)) := by
      have hi : m + (k + 1) + 1 = (m + k + 1) + 1 := by omega
      rw [hi] at h
      exact h
    exact ih (hh.predecessor_up w w' (m + k + 1) hc)
      (fun j hj hk => hup j hj (by omega))

/-- Two consecutive code letters are recovered when the last step is up -/
theorem penultimateCode_of_iso_of_up (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w ((n + 1) + 1))
      (kmswRootedStage w' ((n + 1) + 1))) (hc : w (n + 1) = 1) :
    w n = w' n :=
  lastCode_of_iso w w' n (h.predecessor_up w w' (n + 1) hc)

/-- Two consecutive code letters are recovered through two pendant -/
theorem penultimateCode_of_iso_of_pendant (w w' : ℕ → Fin 3) (n : ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w ((n + 1) + 1))
      (kmswRootedStage w' ((n + 1) + 1))) (hc : w (n + 1) = 2)
    (hUR : (kmswStage w (n + 1)).UR = [])
    (hUR' : (kmswStage w' (n + 1)).UR = []) : w n = w' n :=
  lastCode_of_iso w w' n (h.predecessor_pendant w w' (n + 1) hc hUR hUR')

/-- Two consecutive code letters are recovered through activation -/
theorem penultimateCode_of_iso_of_activation (w w' : ℕ → Fin 3)
    (n e e' : ℕ) (es es' : List ℕ)
    (h : RootedDirectedMapIso (kmswRootedStage w ((n + 1) + 1))
      (kmswRootedStage w' ((n + 1) + 1))) (hc : w (n + 1) = 2)
    (hUR : (kmswStage w (n + 1)).UR = e :: es)
    (hUR' : (kmswStage w' (n + 1)).UR = e' :: es') : w n = w' n :=
  lastCode_of_iso w w' n
    (h.predecessor_activation w w' (n + 1) e e' es es' hc hUR hUR')

/-- A pendant-down root has a singleton head rotation cycle. This is an
intrinsic necessary signal for matching the two down branches -/
theorem kmswRootedStage_pendant_head_fixed (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = []) :
    stageRot w (n + 1) (edgeFlip _ (kmswRootedStage w (n + 1)).root) =
      edgeFlip _ (kmswRootedStage w (n + 1)).root := by
  let s := kmswStage w n
  have hr0 : s.UR = [] := hUR
  have ht : kmswCodeStep (w n) = .down := by rw [hc]; rfl
  have hs : (kmswStage w (n + 1)).nextEdge = s.nextEdge + 1 := by
    change (kmswStep s (w n)).nextEdge = _
    simp only [kmswStep, ht, kmswStepOfStep, hr0, State.addEdge]
  have hr := StageRotation.step_pendant s (act_lt_nextEdge w (le_refl n))
    (stageRotation_UL_bound w n) (stageRot w n) (w n) ht hUR
  have hn := (StageRotation.pendant_new s.nextEdge (stageRot w n)
    (⟨s.active, act_lt_nextEdge w (le_refl n)⟩, true)).2
  apply rot_eq_of_resize hs _ _ hr _ _ _ _ ?_ ?_ hn
  all_goals
    change ((kmswStep s (w n)).active, !false) = (s.nextEdge + 0, true)
    simp only [kmswStep, ht, kmswStepOfStep, hr0, State.addEdge,
      Nat.add_zero, Bool.not_false]

end DirectedDistances.KMSW
