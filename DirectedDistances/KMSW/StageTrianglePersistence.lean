module

public import DirectedDistances.KMSW.StageOuterWordSucc
public import DirectedDistances.KMSW.StageTriangleDarts
public import Mathlib.GroupTheory.Perm.List

/-! # Persistence of KMSW triangle face cycles

Rotation locality away from the outer word, persistence of face successors of
darts off the outer word, and creation-time face cycles of the finite KMSW
Step `j` creates its triangle between stages `j` and `j + 1`; later steps change
the rotation only at darts of the outer word (or at fresh darts). -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem castDart_injective {k l : ℕ} (h : k ≤ l) :
    Function.Injective (outerSucc_castDart h) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ hh
  simp only [outerSucc_castDart, Prod.mk.injEq] at hh
  obtain ⟨h1, h2⟩ := hh
  have h3 : e = f := Fin.ext (by simpa using congrArg Fin.val h1)
  subst h3
  subst h2
  rfl

private theorem stageDart_eq_of_val {k : ℕ} (D T : StageDart k)
    (h : (D.1.val, D.2) = (T.1.val, T.2)) : D = T := by
  rcases D with ⟨e, b⟩
  rcases T with ⟨f, c⟩
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h3 : e = f := Fin.ext h1
  subst h3
  subst h2
  rfl

private theorem stageDart_val_injective (k : ℕ) :
    Function.Injective (fun d : StageDart k => (d.1.val, d.2)) := by
  intro d d' h
  exact stageDart_eq_of_val d d' h

/-- Old darts keep their image when the rotation is only resized -/
private theorem resize_castDart_of_eq {k N : ℕ} (h : N = k)
    (R : Equiv.Perm (StageDart N)) (σ : Equiv.Perm (StageDart k))
    (hR : StageRotation.resize h R = σ) (hkN : k ≤ N) (x : StageDart k) :
    R (outerSucc_castDart hkN x) = outerSucc_castDart hkN (σ x) := by
  subst h
  have hR' : R = σ := hR
  subst hR'
  rfl

/-- Old darts keep their image when the allocated table fixes them -/
private theorem resize_castDart_of_alloc {k r N : ℕ} (h : N = k + r)
    (τ : Equiv.Perm (StageDart (k + r))) (R : Equiv.Perm (StageDart N))
    (hR : StageRotation.resize h R = τ) (σ : Equiv.Perm (StageDart k)) (hkN : k ≤ N)
    (x : StageDart k)
    (htab : τ (StageRotation.allocation k r (.inl x)) =
      StageRotation.allocation k r (.inl (σ x))) :
    R (outerSucc_castDart hkN x) = outerSucc_castDart hkN (σ x) := by
  subst h
  have hR' : R = τ := hR
  subst hR'
  rw [outerSucc_allocation_old k r (Nat.le_add_right k r) x,
    outerSucc_allocation_old k r (Nat.le_add_right k r) (σ x)] at htab
  exact htab

/-- The active west dart is on the outer word, and neither it nor its face
predecessor is off the outer word (`def-kmsw`, -/
private theorem stageRot_ne_active (w : ℕ → Fin 3) (m : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w m,
      (kmswMap w m).faceSucc d = (stageOuterWord w m).formPerm d)
    (x : StageDart (kmswStage w m).nextEdge) (hx : x ∉ stageOuterWord w m)
    (ha : (kmswStage w m).active < (kmswStage w m).nextEdge) :
    x ≠ (⟨(kmswStage w m).active, ha⟩, false) ∧
      stageRot w m x ≠ (⟨(kmswStage w m).active, ha⟩, true) := by
  have hmem : ((⟨(kmswStage w m).active, ha⟩ : Fin (kmswStage w m).nextEdge), false) ∈
      stageOuterWord w m := by
    rw [stageOuterWord_mem_iff]
    left
    refine ⟨rfl, Or.inl ?_⟩
    obtain ⟨es, hes⟩ := kmswStage_UL_last w m
    rw [hes]
    simp
  constructor
  · rintro rfl
    exact hx hmem
  · intro h
    apply hx
    have h1 : (kmswMap w m).faceSucc
        (⟨(kmswStage w m).active, ha⟩, false) = x := by
      apply faceSucc_eq_of_rot_eq
      change stageRot w m x = edgeFlip _ _
      rw [h]
      rfl
    rw [← h1, hcycle _ hmem,
      outerSucc_formPerm_apply_mem_eq_next _ (stageOuterWord_nodup w m) _ hmem]
    exact List.next_mem _ _ hmem

/-- Rotation locality at one step of `def-kmsw`
their rotation image at stage `m + 1`. The hypothesis `hcycle` (the outer word
follows the face permutation) is needed because the rotation tables of the
non-activation branches also modify the dart `rot⁻¹ (active, east)`, which is the
face successor of the active west dart and lies on the outer word precisely by
`hcycle`. -/
theorem stageRot_castDart_of_not_outer (w : ℕ → Fin 3) (m : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w m,
      (kmswMap w m).faceSucc d = (stageOuterWord w m).formPerm d)
    (x : StageDart (kmswStage w m).nextEdge) (hx : x ∉ stageOuterWord w m) :
    stageRot w (m + 1)
        (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m)) x) =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m))
        (stageRot w m x) := by
  have ha := act_lt_nextEdge w (le_refl m)
  obtain ⟨hxa, hxA⟩ := stageRot_ne_active w m hcycle x hx ha
  have hu := stageRotation_UL_bound w m
  cases hc : kmswCodeStep (w m) with
  | down =>
    cases hr : (kmswStage w m).UR with
    | nil =>
      have htab := StageRotation.step_pendant (kmswStage w m) ha hu (stageRot w m)
        (w m) hc hr
      refine resize_castDart_of_alloc _ _ (stageRot w (m + 1)) htab (stageRot w m) _ x ?_
      rw [StageRotation.pendant_old]
      simp only [hxA, ↓reduceIte]
    | cons e es =>
      have htab := StageRotation.step_activation (kmswStage w m) ha hu (stageRot w m)
        (w m) hc e es hr
      exact resize_castDart_of_eq _ (stageRot w (m + 1)) _ htab _ x
  | left =>
    cases hl : (kmswStage w m).UL.dropLast.reverse with
    | nil =>
      have htab := StageRotation.step_leftFresh (kmswStage w m) ha hu (stageRot w m)
        (w m) hc hl
      refine resize_castDart_of_alloc _ _ (stageRot w (m + 1)) htab (stageRot w m) _ x ?_
      rw [StageRotation.leftFresh_old]
      simp only [hxa, hxA, ↓reduceIte]
    | cons e es =>
      have htab := StageRotation.step_leftExisting (kmswStage w m) ha hu (stageRot w m)
        (w m) hc e es hl
      have heUL : e ∈ (kmswStage w m).UL :=
        List.dropLast_subset _ (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self))
      have hxe : x ≠ (⟨e, hu e heUL⟩, false) := by
        intro h
        apply hx
        rw [h, stageOuterWord_mem_iff]
        exact Or.inl ⟨rfl, Or.inl heUL⟩
      refine resize_castDart_of_alloc _ _ (stageRot w (m + 1)) htab (stageRot w m) _ x ?_
      rw [StageRotation.leftExisting_old]
      simp only [hxe, hxA, ↓reduceIte]
  | up =>
    have htab := StageRotation.step_up (kmswStage w m) ha hu (stageRot w m) (w m) hc
    refine resize_castDart_of_alloc _ _ (stageRot w (m + 1)) htab (stageRot w m) _ x ?_
    rw [StageRotation.up_old]
    simp only [hxa, hxA, ↓reduceIte]

/-- Persistence of face successors (`def-kmsw`,
outer word of stage `m`, it is unchanged at stage `m + 1`. -/
theorem stageFaceSucc_castDart_of_not_outer (w : ℕ → Fin 3) (m : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w m,
      (kmswMap w m).faceSucc d = (stageOuterWord w m).formPerm d)
    (d : StageDart (kmswStage w m).nextEdge)
    (hfd : (kmswMap w m).faceSucc d ∉ stageOuterWord w m) :
    (kmswMap w (m + 1)).faceSucc
        (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m)) d) =
      outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m))
        ((kmswMap w m).faceSucc d) :=
  outerSucc_faceSucc_castLE_of_local (kmswStage_nextEdge_mono w (Nat.le_succ m))
    (kmswMap w m) (kmswMap w (m + 1)) d
    (stageRot_castDart_of_not_outer w m hcycle _ hfd)
    (by rcases d with ⟨e, b⟩; rfl)

/-- A face three-cycle of darts off the outer word persists to the next stage -/
theorem faceSucc3Cycle_castDart_of_not_outer (w : ℕ → Fin 3) (m : ℕ)
    (hcycle : ∀ d ∈ stageOuterWord w m,
      (kmswMap w m).faceSucc d = (stageOuterWord w m).formPerm d)
    (d₁ d₂ d₃ : StageDart (kmswStage w m).nextEdge)
    (hc : FaceSucc3Cycle (kmswMap w m).faceSucc d₁ d₂ d₃)
    (h₁ : d₁ ∉ stageOuterWord w m) (h₂ : d₂ ∉ stageOuterWord w m)
    (h₃ : d₃ ∉ stageOuterWord w m) :
    FaceSucc3Cycle (kmswMap w (m + 1)).faceSucc
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m)) d₁)
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m)) d₂)
      (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ m)) d₃) := by
  obtain ⟨e₁, e₂, e₃, n₁, n₂, n₃⟩ := hc
  have hinj := castDart_injective (kmswStage_nextEdge_mono w (Nat.le_succ m))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := stageFaceSucc_castDart_of_not_outer w m hcycle d₁ (by rw [e₁]; exact h₂)
    rwa [e₁] at this
  · have := stageFaceSucc_castDart_of_not_outer w m hcycle d₂ (by rw [e₂]; exact h₃)
    rwa [e₂] at this
  · have := stageFaceSucc_castDart_of_not_outer w m hcycle d₃ (by rw [e₃]; exact h₁)
    rwa [e₃] at this
  · exact fun h => n₁ (hinj h)
  · exact fun h => n₂ (hinj h)
  · exact fun h => n₃ (hinj h)

/-! ### Typed creation triples -/

/-- Triangle dart IDs are allocated at every later stage (`def-kmsw`, -/
theorem stageTriangleDartList_lt (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n) (p : ℕ × Bool)
    (hp : p ∈ stageTriangleDartList w j) : p.1 < (kmswStage w n).nextEdge :=
  stage_face_dart_lt_nextEdge w n p
    (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨j, (mem_stageTriangleTimes w n j).mpr hj, hp⟩))

/-- A dart of the creation triple of `j`, typed at a stage after `j` -/
@[expose] def stageTriangleDartAt (w : ℕ → Fin 3) (n : ℕ) (j : TriangleCreationTime w)
    (hj : j.val < n) (p : ℕ × Bool) (hp : p ∈ stageTriangleDartList w j) :
    StageDart (kmswStage w n).nextEdge :=
  (⟨p.1, stageTriangleDartList_lt w n j hj p hp⟩, p.2)

/-- First dart of `stageTriangleDartTriple`, typed at stage `n` -/
@[expose] def stageTriangleDart₁ (w : ℕ → Fin 3) (n : ℕ) (j : TriangleCreationTime w)
    (hj : j.val < n) : StageDart (kmswStage w n).nextEdge :=
  stageTriangleDartAt w n j hj (stageTriangleDartTriple w j).1
    (by simp [stageTriangleDartList])

/-- Second dart of `stageTriangleDartTriple`, typed at stage `n` -/
@[expose] def stageTriangleDart₂ (w : ℕ → Fin 3) (n : ℕ) (j : TriangleCreationTime w)
    (hj : j.val < n) : StageDart (kmswStage w n).nextEdge :=
  stageTriangleDartAt w n j hj (stageTriangleDartTriple w j).2.1
    (by simp [stageTriangleDartList])

/-- Third dart of `stageTriangleDartTriple`, typed at stage `n` -/
@[expose] def stageTriangleDart₃ (w : ℕ → Fin 3) (n : ℕ) (j : TriangleCreationTime w)
    (hj : j.val < n) : StageDart (kmswStage w n).nextEdge :=
  stageTriangleDartAt w n j hj (stageTriangleDartTriple w j).2.2
    (by simp [stageTriangleDartList])

private theorem faceSucc3Cycle_resize {N a : ℕ} (h : N = a)
    (R : Equiv.Perm (StageDart N)) (τ : Equiv.Perm (StageDart a))
    (hR : StageRotation.resize h R = τ) (d₁ d₂ d₃ : StageDart a)
    (hc : FaceSucc3Cycle (stageRotationMap a τ).faceSucc d₁ d₂ d₃) :
    FaceSucc3Cycle (stageRotationMap N R).faceSucc
      (outerSucc_castDart h.ge d₁) (outerSucc_castDart h.ge d₂)
      (outerSucc_castDart h.ge d₃) := by
  subst h
  have hR' : R = τ := hR
  subst hR'
  exact hc

private theorem faceSucc3Cycle_congr {D : Type*} {f : Equiv.Perm D} {a b c a' b' c' : D}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (h : FaceSucc3Cycle f a b c) : FaceSucc3Cycle f a' b' c' := by
  subst ha
  subst hb
  subst hc
  exact h

private theorem formPerm_map_consec {α β : Type*} [DecidableEq α] (f : α → β)
    (W : List α) (hnd : W.Nodup) (P Q : List β) (x y : β)
    (hV : W.map f = P ++ x :: y :: Q) :
    ∃ a ∈ W, ∃ b, f a = x ∧ f b = y ∧ W.formPerm a = b := by
  have hlen : P.length + 1 < W.length := by
    have := congrArg List.length hV
    simp at this
    omega
  have hmap : P.length < (W.map f).length := by simp; omega
  have hmap1 : P.length + 1 < (W.map f).length := by simp; omega
  refine ⟨W[P.length], List.getElem_mem _, W[P.length + 1], ?_, ?_, ?_⟩
  · have := List.getElem_of_eq hV hmap
    simpa using this
  · have := List.getElem_of_eq hV hmap1
    simpa using this
  · exact List.formPerm_apply_lt_getElem W hnd P.length hlen

/-- For an existing-predecessor left step, the outer-word cycle property gives
the corner equation: `(e, west)` and `(active, west)` are consecutive in the
outer word (`UL = es.reverse ++ [e, active]`), so `rot (active, west) = (e, east)` -/
private theorem leftExisting_corner (w : ℕ → Fin 3) (m : ℕ) (e : ℕ) (es : List ℕ)
    (hl : (kmswStage w m).UL.dropLast.reverse = e :: es)
    (he : e < (kmswStage w m).nextEdge) (ha : (kmswStage w m).active < (kmswStage w m).nextEdge)
    (hcycle : ∀ d ∈ stageOuterWord w m,
      (kmswMap w m).faceSucc d = (stageOuterWord w m).formPerm d) :
    e ≠ (kmswStage w m).active ∧
      stageRot w m (⟨(kmswStage w m).active, ha⟩, false) = (⟨e, he⟩, true) := by
  have hdrop : (kmswStage w m).UL.dropLast = es.reverse ++ [e] := by
    have h := congrArg List.reverse hl
    simpa only [List.reverse_cons, List.reverse_reverse] using h
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
  have hxsDrop : xs = (kmswStage w m).UL.dropLast := by rw [hxs]; simp
  have hUL : (kmswStage w m).UL = es.reverse ++ [e, (kmswStage w m).active] := by
    calc
      (kmswStage w m).UL = xs ++ [(kmswStage w m).active] := hxs
      _ = (kmswStage w m).UL.dropLast ++ [(kmswStage w m).active] := by rw [← hxsDrop]
      _ = (es.reverse ++ [e]) ++ [(kmswStage w m).active] := by rw [hdrop]
      _ = es.reverse ++ [e, (kmswStage w m).active] := by simp [List.append_assoc]
  have hVW : stageOuterWordVal w m =
      es.reverse.map (fun f => (f, false)) ++
        ((e, false) :: ((kmswStage w m).active, false) ::
          (((kmswStage w m).UR.map (fun f => (f, false)) ++
            (kmswStage w m).LR.reverse.map (fun f => (f, true))) ++
            (kmswStage w m).LL.reverse.map (fun f => (f, true)))) := by
    rw [stageOuterWordVal_eq_runs, hUL]
    simp [List.map_append, List.append_assoc]
  have hnd : (stageOuterWordVal w m).Nodup :=
    (stageOuterWord_nodup w m).map (stageDart_val_injective _)
  have hne : e ≠ (kmswStage w m).active := by
    rw [hVW] at hnd
    have h2 := hnd.of_append_right
    rw [List.nodup_cons] at h2
    intro h
    apply h2.1
    subst h
    simp
  refine ⟨hne, ?_⟩
  obtain ⟨a, hamem, b, ha1, hb1, hab⟩ := formPerm_map_consec
    (fun d : StageDart (kmswStage w m).nextEdge => (d.1.val, d.2))
    (stageOuterWord w m) (stageOuterWord_nodup w m) _ _ _ _
    (show (stageOuterWord w m).map (fun d : StageDart (kmswStage w m).nextEdge =>
      (d.1.val, d.2)) = _ from hVW)
  have haeq : a = (⟨e, he⟩, false) := stageDart_eq_of_val _ _ ha1
  have hbeq : b = (⟨(kmswStage w m).active, ha⟩, false) := stageDart_eq_of_val _ _ hb1
  have hfs := (hcycle a hamem).trans hab
  rw [haeq, hbeq] at hfs
  have hrot : (kmswMap w m).rot ((kmswMap w m).faceSucc (⟨e, he⟩, false)) =
      (kmswMap w m).edgeInv (⟨e, he⟩, false) :=
    (kmswMap w m).rot.apply_symm_apply _
  rw [hfs] at hrot
  exact hrot

/-- `stageTriangleDartTriple w j`, typed at stage `j + 1`, is a face three-cycle of
`(kmswMap w (j + 1)).faceSucc`. For an existing-predecessor left step the corner
equation is discharged from `hcycle` at stage `j`. -/
theorem stageTriangle_creation (w : ℕ → Fin 3) (j : TriangleCreationTime w)
    (hcycle : ∀ d ∈ stageOuterWord w j.val,
      (kmswMap w j.val).faceSucc d = (stageOuterWord w j.val).formPerm d) :
    FaceSucc3Cycle (kmswMap w (j.val + 1)).faceSucc
      (stageTriangleDart₁ w (j.val + 1) j (Nat.lt_succ_self _))
      (stageTriangleDart₂ w (j.val + 1) j (Nat.lt_succ_self _))
      (stageTriangleDart₃ w (j.val + 1) j (Nat.lt_succ_self _)) := by
  have ha := act_lt_nextEdge w (le_refl j.val)
  have hu := stageRotation_UL_bound w j.val
  rcases j.property with h0 | h1
  · have hcode : kmswCodeStep (w j.val) = .left := by simp [kmswCodeStep, h0]
    cases hl : (kmswStage w j.val).UL.dropLast.reverse with
    | nil =>
      have htab := StageRotation.step_leftFresh (kmswStage w j.val) ha hu
        (stageRot w j.val) (w j.val) hcode hl
      have ht := stageTriangleDartTriple_left_fresh w j h0 hl
      have cyc := leftFresh_triangle_face_cycle (kmswStage w j.val).nextEdge
        (stageRot w j.val) ⟨(kmswStage w j.val).active, ha⟩
      dsimp only at cyc
      have key := faceSucc3Cycle_resize _ (stageRot w (j.val + 1)) _ htab _ _ _ cyc
      exact faceSucc3Cycle_congr
        (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.1) ht).symm))
        (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.2.1) ht).symm))
        (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.2.2) ht).symm)) key
    | cons e es =>
      have htab := StageRotation.step_leftExisting (kmswStage w j.val) ha hu
        (stageRot w j.val) (w j.val) hcode e es hl
      have ht := stageTriangleDartTriple_left_existing w j h0 e es hl
      have heUL : e ∈ (kmswStage w j.val).UL :=
        List.dropLast_subset _ (List.mem_reverse.mp (by rw [hl]; exact List.mem_cons_self))
      have he := hu e heUL
      obtain ⟨hne, hcorner⟩ := leftExisting_corner w j.val e es hl he ha hcycle
      have cyc := leftExisting_triangle_face_cycle (kmswStage w j.val).nextEdge
        (stageRot w j.val) ⟨e, he⟩ ⟨(kmswStage w j.val).active, ha⟩
        (fun h => hne (congrArg Fin.val h)) hcorner
      dsimp only at cyc
      have key := faceSucc3Cycle_resize _ (stageRot w (j.val + 1)) _ htab _ _ _ cyc
      exact faceSucc3Cycle_congr
        (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.1) ht).symm))
        (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.2.1) ht).symm))
        (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.2.2) ht).symm)) key
  · have hcode : kmswCodeStep (w j.val) = .up := by simp [kmswCodeStep, h1]
    have htab := StageRotation.step_up (kmswStage w j.val) ha hu
      (stageRot w j.val) (w j.val) hcode
    have ht := stageTriangleDartTriple_up w j h1
    have cyc := up_triangle_face_cycle (kmswStage w j.val).nextEdge
      (stageRot w j.val) ⟨(kmswStage w j.val).active, ha⟩
    dsimp only at cyc
    have key := faceSucc3Cycle_resize _ (stageRot w (j.val + 1)) _ htab _ _ _ cyc
    exact faceSucc3Cycle_congr
      (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.1) ht).symm))
      (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.2.1) ht).symm))
      (stageDart_eq_of_val _ _ (by exact (congrArg (fun t => t.2.2) ht).symm)) key

/-- The typed creation triple of `j` is a face three-cycle at every later stage
followed by persistence, since triangle darts are never on the outer word. -/
theorem stageTriangle_faceSucc3Cycle (w : ℕ → Fin 3)
    (hcycle : ∀ n, ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (j : TriangleCreationTime w) (n : ℕ) (hj : j.val < n) :
    FaceSucc3Cycle (kmswMap w n).faceSucc
      (stageTriangleDart₁ w n j hj) (stageTriangleDart₂ w n j hj)
      (stageTriangleDart₃ w n j hj) := by
  induction n, (hj : j.val + 1 ≤ n) using Nat.le_induction with
  | base => exact stageTriangle_creation w j (hcycle j.val)
  | succ n hn ih =>
    exact faceSucc3Cycle_castDart_of_not_outer w n (hcycle n) _ _ _ ih
      (stageTriangleDart_not_outer w n j hn _
        (by simp [stageTriangleDartList, stageTriangleDart₁, stageTriangleDartAt]))
      (stageTriangleDart_not_outer w n j hn _
        (by simp [stageTriangleDartList, stageTriangleDart₂, stageTriangleDartAt]))
      (stageTriangleDart_not_outer w n j hn _
        (by simp [stageTriangleDartList, stageTriangleDart₃, stageTriangleDartAt]))

end DirectedDistances.KMSW
