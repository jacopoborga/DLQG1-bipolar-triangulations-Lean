module

public import DirectedDistances.KMSW.KMSWLeftSimState
public import DirectedDistances.KMSW.StageFaceDetermination
public import DirectedDistances.PlanarMap.DirectedMapMarkMissing
public import DirectedDistances.KMSW.StageOuterCycle
public import DirectedDistances.KMSW.StageBoundaryMap
public import DirectedDistances.KMSW.KMSWLeftDirectRun

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap DirectedDistances.RandomWalk

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
theorem kmswLeftSimEdge_agree (r : ℕ) (u : ℕ → Fin 3) (m n e : ℕ)
    (hmn : m ≤ n) (he : e < (kmswStage u m).nextEdge) :
    kmswLeftSimEdge r u n e = kmswLeftSimEdge r u m e := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [kmswLeftSimEdge_succ_agree r u n e
      (he.trans_le (kmswStage_nextEdge_mono u hmn)), ih]

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
theorem kmswLeftSim_outer_word (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (hterminal : (kmswStage u n).LL.length = r - 1) :
    (stageOuterWordVal u n).map (fun p => (kmswLeftSimEdge r u n p.1, p.2)) =
      stageOuterWordVal (kmswLeftPrefixed r u) (r - 1 + n) := by
  obtain ⟨_, _, _, _, _, _, _, hlr, hul, hur, hll⟩ :=
    kmswLeftSim_terminal_bijective r u hr n hquad hterminal
  rw [stageOuterWordVal_eq_runs, stageOuterWordVal_eq_runs, hlr, hul, hur, hll]
  simp only [List.map_append, List.map_map, List.reverse_append, ← List.map_reverse,
    List.reverse_nil, List.map_nil, List.append_nil, List.append_assoc]
  rfl

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
@[expose] noncomputable def kmswLeftSimEdgeEquiv (r : ℕ) (u : ℕ → Fin 3)
    (hr : 1 ≤ r) (n : ℕ) (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (hterminal : (kmswStage u n).LL.length = r - 1) :
    Fin (kmswStage u n).nextEdge ≃
      Fin (kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).nextEdge := by
  obtain ⟨hb, hi, hs, _⟩ :=
    kmswLeftSim_terminal_bijective r u hr n hquad hterminal
  exact Equiv.ofBijective (fun e => ⟨kmswLeftSimEdge r u n e.val, hb e.val e.isLt⟩)
    ⟨fun e f hef => Fin.ext (hi e.val e.isLt f.val f.isLt (congrArg Fin.val hef)),
      fun f => by
        obtain ⟨e, he, hef⟩ := hs f.val f.isLt
        exact ⟨⟨e, he⟩, Fin.ext hef⟩⟩

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
theorem kmswLeftSimEdgeEquiv_val (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (hterminal : (kmswStage u n).LL.length = r - 1)
    (e : Fin (kmswStage u n).nextEdge) :
    (kmswLeftSimEdgeEquiv r u hr n hquad hterminal e).val =
      kmswLeftSimEdge r u n e.val := rfl

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
theorem kmswLeftSim_markMissing_outer (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r)
    (n : ℕ) (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k) :
    ∀ d ∈ ({d | d.1.val < r - 1} :
      Set (StageDart (kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).nextEdge)),
      (kmswStageDirectedMap (kmswLeftPrefixed r u) (r - 1 + n)).IsOuter d ∨
        (kmswStageDirectedMap (kmswLeftPrefixed r u) (r - 1 + n)).IsOuter
          ((kmswStageDirectedMap (kmswLeftPrefixed r u) (r - 1 + n)).edgeInv d) := by
  intro ⟨e, b⟩ he
  have h := kmswLeftSim_of_quadrant r u hr n hquad
  have hmem : e.val ∈ (kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).LR := by
    rw [h.lr]
    exact List.mem_append_left _ (List.mem_range.mpr he)
  have ho := ((kmswStageDirectedMap_LR_bridge (kmswLeftPrefixed r u)
    (r - 1 + n) e).mp hmem).2.2
  cases b
  · exact Or.inr ho
  · exact Or.inl ho

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
theorem kmswLeftSim_triangle_succ (r : ℕ) (u : ℕ → Fin 3) (m : ℕ)
    (hc : u m = 0 ∨ u m = 1)
    (h : KMSWLeftSim r (kmswStage u m)
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + m))
      (kmswLeftSimEdge r u m) (kmswLeftSimVertex r u m))
    (hLL : (kmswStage u (m + 1)).LL.length ≤ r - 1) :
    List.IsRotated
      ((stageTriangleDartList u ⟨m, hc⟩).map
        (fun p => (kmswLeftSimEdge r u (m + 1) p.1, p.2)))
      (stageTriangleDartList (kmswLeftPrefixed r u)
        ⟨r - 1 + m, by simpa only [kmswLeftPrefixed_suffix] using hc⟩) := by
  let S := kmswStage u m
  let T := kmswStage (kmswLeftPrefixed r u) (r - 1 + m)
  let φ := kmswLeftSimEdge r u m
  let j := r - 1 - S.LL.length
  let F := kmswLeftSimEdge r u (m + 1)
  change KMSWLeftSim r S T φ (kmswLeftSimVertex r u m) at h
  have ha : S.active < S.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u m).1
  have hFa : F S.active = φ S.active := kmswLeftSimEdge_succ_agree r u m _ ha
  have hFnew : F S.nextEdge = T.nextEdge := by
    change kmswLeftExtEdge S (u m) j φ S.nextEdge = T.nextEdge
    simp only [kmswLeftExtEdge, lt_self_iff_false, ↓reduceIte,
      show S.nextEdge ≠ S.nextEdge + 1 by omega, and_false]
    exact h.nextEdge.symm
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last u m
  change S.UL = xs ++ [S.active] at hxs
  rcases hc with hc | hc
  · have hcode : kmswCodeStep (u m) = .left := by rw [hc]; rfl
    by_cases hx : xs = []
    · have hSUL : S.UL = [S.active] := by simpa only [hx, List.nil_append] using hxs
      have hdrop : S.UL.dropLast = [] := by rw [hSUL]; rfl
      have hstack : S.UL.dropLast.reverse = [] := by rw [hdrop]; rfl
      have hj : 0 < j := by
        have hh : (kmswStage u (m + 1)).LL.length = S.LL.length + 1 := by
          simp only [kmswStage, kmswStep, hcode]
          change (kmswStepOfStep S .left).LL.length = _
          simp only [kmswStepOfStep, hstack, State.addEdge, List.length_cons]
        dsimp only [j]
        omega
      have hTUL : T.UL = List.range j ++ [φ S.active] := by
        simpa only [hSUL, List.map_cons, List.map_nil] using h.ul
      have hTstack : T.UL.dropLast.reverse =
          (j - 1) :: (List.range (j - 1)).reverse := by
        rw [hTUL, List.dropLast_concat, show j = (j - 1) + 1 by omega,
          List.range_succ]
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          Nat.add_sub_cancel]
      have hFnew1 : F (S.nextEdge + 1) = j - 1 := by
        change kmswLeftExtEdge S (u m) j φ (S.nextEdge + 1) = j - 1
        simp only [kmswLeftExtEdge, show ¬ S.nextEdge + 1 < S.nextEdge by omega,
          ↓reduceIte, hcode, hdrop, and_self]
      have hcT : kmswLeftPrefixed r u (r - 1 + m) = 0 :=
        (kmswLeftPrefixed_suffix r u m).trans hc
      simp only [stageTriangleDartList, stageTriangleDartTriple, hc, hcT, ↓reduceIte]
      change List.IsRotated
        (let t := match S.UL.dropLast.reverse with
          | e :: _ => ((e, false), (S.active, false), (S.nextEdge, true))
          | [] => ((S.active, false), (S.nextEdge, true), (S.nextEdge + 1, false))
         [t.1, t.2.1, t.2.2].map (fun p => (F p.1, p.2)))
        (let t := match T.UL.dropLast.reverse with
          | e :: _ => ((e, false), (T.active, false), (T.nextEdge, true))
          | [] => ((T.active, false), (T.nextEdge, true), (T.nextEdge + 1, false))
         [t.1, t.2.1, t.2.2])
      rw [hstack, hTstack]
      simp only [List.map_cons, List.map_nil, hFa, hFnew, hFnew1, h.active]
      exact ⟨2, rfl⟩
    · let e := xs.getLast hx
      let ys := xs.dropLast
      have hsplit : ys ++ [e] = xs := List.dropLast_append_getLast hx
      have hSUL : S.UL = ys ++ [e, S.active] := by
        rw [hxs, ← hsplit, List.append_assoc]
        rfl
      have he : e < S.nextEdge :=
        (kmswStage_boundary_ids_lt_nextEdge u m).2 e (by
          change e ∈ S.UL ++ S.UR ++ S.LL ++ S.LR
          rw [hSUL]
          simp only [List.mem_append, List.mem_cons]
          tauto)
      have hFe : F e = φ e := kmswLeftSimEdge_succ_agree r u m e he
      have hSstack : S.UL.dropLast.reverse = e :: ys.reverse := by
        rw [hSUL, List.dropLast_append_cons]
        simp only [List.dropLast_cons_cons, List.dropLast_singleton,
          List.reverse_append, List.reverse_singleton, List.singleton_append]
      have hTUL : T.UL =
          ((List.range j ++ ys.map φ) ++ [φ e]) ++ [φ S.active] := by
        rw [h.ul, hSUL]
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append]
        rfl
      have hTstack : T.UL.dropLast.reverse =
          φ e :: (List.range j ++ ys.map φ).reverse := by
        rw [hTUL, List.dropLast_concat]
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
      have hcT : kmswLeftPrefixed r u (r - 1 + m) = 0 :=
        (kmswLeftPrefixed_suffix r u m).trans hc
      simp only [stageTriangleDartList, stageTriangleDartTriple, hc, hcT, ↓reduceIte]
      change List.IsRotated
        (let t := match S.UL.dropLast.reverse with
          | e :: _ => ((e, false), (S.active, false), (S.nextEdge, true))
          | [] => ((S.active, false), (S.nextEdge, true), (S.nextEdge + 1, false))
         [t.1, t.2.1, t.2.2].map (fun p => (F p.1, p.2)))
        (let t := match T.UL.dropLast.reverse with
          | e :: _ => ((e, false), (T.active, false), (T.nextEdge, true))
          | [] => ((T.active, false), (T.nextEdge, true), (T.nextEdge + 1, false))
         [t.1, t.2.1, t.2.2])
      rw [hSstack, hTstack]
      simp only [List.map_cons, List.map_nil, hFe, hFa, hFnew, h.active]
      exact List.IsRotated.refl _
  · have hFnew1 : F (S.nextEdge + 1) = T.nextEdge + 1 := by
      have hcode : kmswCodeStep (u m) = .up := by rw [hc]; rfl
      change kmswLeftExtEdge S (u m) j φ (S.nextEdge + 1) = T.nextEdge + 1
      simp only [kmswLeftExtEdge, show ¬ S.nextEdge + 1 < S.nextEdge by omega,
        ↓reduceIte, hcode, reduceCtorEq, false_and]
      have hh := h.nextEdge
      change T.nextEdge = S.nextEdge + j at hh
      omega
    have hcT : kmswLeftPrefixed r u (r - 1 + m) = 1 :=
      (kmswLeftPrefixed_suffix r u m).trans hc
    have h0 : u m ≠ 0 := by rw [hc]; decide
    have hT0 : kmswLeftPrefixed r u (r - 1 + m) ≠ 0 := by rw [hcT]; decide
    simp only [stageTriangleDartList, stageTriangleDartTriple, h0, hT0, ↓reduceIte]
    change List.IsRotated
      ([(S.active, false), (S.nextEdge + 1, true), (S.nextEdge, true)].map
        (fun p => (F p.1, p.2)))
      [(T.active, false), (T.nextEdge + 1, true), (T.nextEdge, true)]
    simp only [List.map_cons, List.map_nil, hFa, hFnew, hFnew1, h.active]
    exact List.IsRotated.refl _

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
theorem kmswLeftSim_triangle (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (j : TriangleCreationTime u) (hj : j.val < n) :
    List.IsRotated
      ((stageTriangleDartList u j).map (fun p => (kmswLeftSimEdge r u n p.1, p.2)))
      (stageTriangleDartList (kmswLeftPrefixed r u)
        ⟨r - 1 + j.val, by simpa only [kmswLeftPrefixed_suffix] using j.property⟩) := by
  have h := kmswLeftSim_of_quadrant r u hr j.val (fun k hk => hquad k (by omega))
  have hLL := kmswLeftSim_LL_bound r u hr (j.val + 1)
    (fun k hk => hquad k (by omega))
  have heq : (stageTriangleDartList u j).map
      (fun p => (kmswLeftSimEdge r u n p.1, p.2)) =
      (stageTriangleDartList u j).map
        (fun p => (kmswLeftSimEdge r u (j.val + 1) p.1, p.2)) := by
    apply List.map_congr_left
    intro p hp
    have hb := stage_face_dart_lt_nextEdge u (j.val + 1) p
      (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨j, (mem_stageTriangleTimes u (j.val + 1) j).mpr (by omega), hp⟩))
    rw [kmswLeftSimEdge_agree r u (j.val + 1) n p.1 (by omega) hb]
  rw [heq]
  exact kmswLeftSim_triangle_succ r u j.val j.property h hLL

private theorem terminal_status (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (ht : (kmswStage u n).LL.length = r - 1) (hUR : (kmswStage u n).UR = [])
    (e : ℕ) (he : e < (kmswStage u n).nextEdge) :
    (kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).present
        (kmswLeftSimEdge r u n e) = true ∧
      ((kmswStage u n).present e = false ↔ kmswLeftSimEdge r u n e < r - 1) := by
  have h := kmswLeftSim_of_quadrant r u hr n hquad
  obtain ⟨_, hi, _, _, _, _, hll, _⟩ := h.terminal_bijective ht
  have hmissing := kmswLeftSim_missing_iff_ur r u hr n hquad e he
  rw [hUR] at hmissing
  constructor
  · cases hp : (kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).present
        (kmswLeftSimEdge r u n e)
    · exact False.elim (List.not_mem_nil (hmissing.mp hp))
    · rfl
  · have hm := (kmswStage_status u n).1 e he
    rw [hUR] at hm
    simp only [List.not_mem_nil, false_or] at hm
    rw [hm]
    constructor
    · intro heLL
      apply List.mem_range.mp
      rw [← hll]
      exact List.mem_map.mpr ⟨e, heLL, rfl⟩
    · intro hsmall
      have hmem : kmswLeftSimEdge r u n e ∈ List.range (r - 1) :=
        List.mem_range.mpr hsmall
      rw [← hll] at hmem
      obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hmem
      have hfb := (kmswStage_boundary_ids_lt_nextEdge u n).2 f (by
        simp only [List.mem_append]
        tauto)
      have hEq := hi f hfb e he hfe
      simpa only [hEq] using hf

private theorem sameCycle_equiv {α β : Type*} [Fintype α] [Fintype β]
    (φ : α ≃ β) (f : Equiv.Perm α) (g : Equiv.Perm β)
    (h : ∀ x, φ (f x) = g (φ x)) (x y : α) :
    g.SameCycle (φ x) (φ y) ↔ f.SameCycle x y := by
  have hp (k : ℕ) (z : α) : φ ((f ^ k) z) = (g ^ k) (φ z) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [pow_succ', Equiv.Perm.mul_apply, h, ih]
  constructor
  · intro hc
    obtain ⟨k, _, hk⟩ := hc.exists_pow_eq'
    exact ⟨(k : ℤ), by
      rw [zpow_natCast]
      apply φ.injective
      rw [hp, hk]⟩
  · intro hc
    obtain ⟨k, _, hk⟩ := hc.exists_pow_eq'
    exact ⟨(k : ℤ), by rw [zpow_natCast, ← hp, hk]⟩

private theorem terminal_outer_dart (r : ℕ) (u : ℕ → Fin 3) (hr : 1 ≤ r) (n : ℕ)
    (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (ht : (kmswStage u n).LL.length = r - 1) :
    Equiv.prodCongr (kmswLeftSimEdgeEquiv r u hr n hquad ht) (Equiv.refl Bool)
        (stageULHeadDart u n) =
      stageULHeadDart (kmswLeftPrefixed r u) (r - 1 + n) := by
  obtain ⟨_, _, _, _, _, _, _, _, hul, _, _⟩ :=
    kmswLeftSim_terminal_bijective r u hr n hquad ht
  apply Prod.ext
  · apply Fin.ext
    change kmswLeftSimEdge r u n
        ((kmswStage u n).UL.head (kmswStage_UL_nonempty_active_last u n).1) =
      (kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).UL.head _
    simp only [hul, List.head_map]
  · rfl

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
@[expose] noncomputable def kmswLeftSimMapIso (r : ℕ) (u : ℕ → Fin 3)
    (hr : 1 ≤ r) (n : ℕ) (hquad : ∀ k ≤ n, 0 ≤ (r : ℤ) - 1 + L u k)
    (hterminal : (kmswStage u n).LL.length = r - 1)
    (hUR : (kmswStage u n).UR = []) :
    DirectedMapWithMissingIso (kmswStageDirectedMap u n)
      ((kmswStageDirectedMap (kmswLeftPrefixed r u) (r - 1 + n)).markMissing
        {d | d.1.val < r - 1} (kmswLeftSim_markMissing_outer r u hr n hquad)) :=
  let φF := kmswLeftSimEdgeEquiv r u hr n hquad hterminal
  let Φ := Equiv.prodCongr φF (Equiv.refl Bool)
  have hfaces := kmswMap_conj_of_faces u (kmswLeftPrefixed r u) n (r - 1 + n)
    φF (kmswLeftSimEdge r u n) (fun _ => rfl)
    (by rw [kmswLeftSim_outer_word r u hr n hquad hterminal])
    (by
      intro j hj
      refine ⟨⟨r - 1 + j.val, ?_⟩, by dsimp only; omega,
        kmswLeftSim_triangle r u hr n hquad j hj⟩
      simpa only [kmswLeftPrefixed_suffix] using j.property)
  {
    toEquiv := Φ
    rot_comm := hfaces.2.1
    edgeInv_comm := hfaces.2.2
    missing_iff := by
      rintro ⟨e, b⟩
      obtain ⟨hp, hs⟩ := terminal_status r u hr n hquad hterminal hUR e.val e.isLt
      change
        (kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).present
            (kmswLeftSimEdge r u n e.val) = false ∨
          kmswLeftSimEdge r u n e.val < r - 1 ∨
          kmswLeftSimEdge r u n e.val < r - 1 ↔
        (kmswStage u n).present e.val = false
      rw [hp]
      simpa only [Bool.true_eq_false, false_or, or_self] using hs.symm
    tail_iff := by
      rintro ⟨e, b⟩
      obtain ⟨hp, hs⟩ := terminal_status r u hr n hquad hterminal hUR e.val e.isLt
      have ht : (kmswStage u n).present e.val = true ↔
          ¬ kmswLeftSimEdge r u n e.val < r - 1 := by
        rw [← hs]
        cases (kmswStage u n).present e.val <;> simp
      change
        ((kmswStage (kmswLeftPrefixed r u) (r - 1 + n)).present
            (kmswLeftSimEdge r u n e.val) = true ∧ b = false) ∧
          ¬ (kmswLeftSimEdge r u n e.val < r - 1 ∨
            kmswLeftSimEdge r u n e.val < r - 1) ↔
        (kmswStage u n).present e.val = true ∧ b = false
      rw [hp]
      simp only [true_and, or_self]
      rw [← ht]
      exact and_comm
    outer_iff := by
      intro d
      change (kmswMap (kmswLeftPrefixed r u) (r - 1 + n)).faceSucc.SameCycle
          (stageULHeadDart (kmswLeftPrefixed r u) (r - 1 + n)) (Φ d) ↔
        (kmswMap u n).faceSucc.SameCycle (stageULHeadDart u n) d
      rw [← terminal_outer_dart r u hr n hquad hterminal]
      exact sameCycle_equiv Φ _ _ hfaces.1 _ d }

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
theorem kmswLeftRun_admissible_quadrant (ℓ n : ℕ) (c : Fin n → Fin 3)
    (hc : KMSWLeftWalkAdmissible ℓ n c) :
    ∀ k ≤ n, 0 ≤ (ℓ : ℤ) - 1 + L (finiteCodeExtend (n := n + 1) c) k := by
  intro k hk
  rw [kmsw_L_eq]
  exact (hc.2 k (Finset.mem_range.mpr (by omega))).1

/-- coincides with the prefixed run with its first r−1 right-boundary edges declared missing; -/
theorem kmswLeftRun_admissible_mapIso (ℓ n : ℕ) (c : KMSWLeftWalkClass ℓ n)
    (hℓ : 1 ≤ ℓ) :
    let u := finiteCodeExtend (n := n + 1) c.val
    Nonempty (DirectedMapWithMissingIso (kmswStageDirectedMap u n)
      ((kmswStageDirectedMap (kmswLeftPrefixed ℓ u) (ℓ - 1 + n)).markMissing
        {d | d.1.val < ℓ - 1}
        (kmswLeftSim_markMissing_outer ℓ u hℓ n
          (kmswLeftRun_admissible_quadrant ℓ n c.val c.property)))) := by
  dsimp only
  obtain ⟨hUR, _, hLL, _⟩ := kmswLeftRun_admissible_lengths ℓ n c.val c.property
  exact ⟨kmswLeftSimMapIso ℓ (finiteCodeExtend (n := n + 1) c.val) hℓ n
    (kmswLeftRun_admissible_quadrant ℓ n c.val c.property) hLL
    (List.length_eq_zero_iff.mp hUR)⟩

end DirectedDistances.KMSW
