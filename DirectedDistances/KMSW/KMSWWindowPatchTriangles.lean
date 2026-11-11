module

public import DirectedDistances.KMSW.KMSWWindowPatchRelation
public import DirectedDistances.KMSW.StageTriangleDarts

 

public section
namespace DirectedDistances.KMSW

 
structure KMSWWindowPatchData where
  φ : ℕ → ℕ
  A : List ℕ
  B : List ℕ
  YL : List ℕ
  YR : List ℕ
  XL : List ℕ
  XR : List ℕ

 
@[expose] def KMSWWindowPatchData.step (G F : State) (c : Step)
    (d : KMSWWindowPatchData) : KMSWWindowPatchData :=
  let alloc := fun e => if e < F.nextEdge then d.φ e else G.nextEdge + (e - F.nextEdge)
  match c with
  | .down => match F.UR with
    | _ :: _ => d
    | [] => match d.B with
      | [] => { d with φ := alloc, XR := d.XR ++ [F.nextEdge] }
      | q :: bs =>
        { d with
          φ := fun e => if e < F.nextEdge then d.φ e else q
          B := bs
          YR := d.YR ++ [F.nextEdge] }
  | .up => { d with φ := alloc }
  | .left => match F.UL.dropLast.reverse with
    | _ :: _ => { d with φ := alloc }
    | [] => match d.A.reverse with
      | [] => { d with φ := alloc, XL := (F.nextEdge + 1) :: d.XL }
      | q :: es =>
        { d with
          φ := fun e => if e < F.nextEdge then d.φ e else
            if e = F.nextEdge then G.nextEdge else q
          A := es.reverse
          YL := (F.nextEdge + 1) :: d.YL }

 
@[expose] def kmswWindowPatchData (w : ℕ → Fin 3) (s : ℕ) : ℕ → KMSWWindowPatchData
  | 0 => ⟨fun _ => (kmswStage w s).active,
      (kmswStage w s).UL.dropLast, (kmswStage w s).UR, [], [], [], []⟩
  | j + 1 => KMSWWindowPatchData.step (kmswStage w (s + j))
      (kmswStage (fun i => w (s + i)) j) (kmswCodeStep (w (s + j)))
      (kmswWindowPatchData w s j)

private theorem patchStep_rel {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {d : KMSWWindowPatchData}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) d.φ d.A d.B d.YL d.YR d.XL d.XR)
    (c : Step) :
    let d' := KMSWWindowPatchData.step G (kmswStage u j) c d
    KMSWWindowPatchRel G₀ (kmswStepOfStep G c) (kmswStepOfStep (kmswStage u j) c)
      d'.φ d'.A d'.B d'.YL d'.YR d'.XL d'.XR := by
  cases d with
  | mk φ A B YL YR XL XR =>
    cases c with
    | down =>
      cases hu : (kmswStage u j).UR with
      | cons e es =>
        simpa only [KMSWWindowPatchData.step, hu] using
          kmswWindowPatchRel_down_existing h e es hu
      | nil =>
        cases B with
        | nil =>
          simpa only [KMSWWindowPatchData.step, hu] using
            kmswWindowPatchRel_down_fresh h hu
        | cons q bs =>
          simpa only [KMSWWindowPatchData.step, hu] using
            kmswWindowPatchRel_down_seam h hu
    | up => exact kmswWindowPatchRel_up h
    | left =>
      cases hs : (kmswStage u j).UL.dropLast.reverse with
      | cons e es =>
        simpa only [KMSWWindowPatchData.step, hs] using kmswWindowPatchRel_left_existing h e es hs
      | nil =>
        have hs' : (kmswStage u j).UL.dropLast = [] := by
          have hh := congrArg List.reverse hs
          simpa only [List.reverse_reverse, List.reverse_nil] using hh
        cases ha : A.reverse with
        | nil =>
          have ha' : A = [] := List.reverse_eq_nil_iff.mp ha
          subst A
          simpa only [KMSWWindowPatchData.step, hs, List.reverse_nil] using
            kmswWindowPatchRel_left_fresh h hs'
        | cons q es =>
          have ha' : A = es.reverse ++ [q] := by
            have hh := congrArg List.reverse ha
            simpa only [List.reverse_reverse, List.reverse_cons] using hh
          have h' := h
          change KMSWWindowPatchRel _ _ _ φ A B YL YR XL XR at h'
          rw [ha'] at h'
          simpa only [KMSWWindowPatchData.step, hs, ha] using kmswWindowPatchRel_left_seam h' hs'

 
theorem kmswWindowPatchData_rel (w : ℕ → Fin 3) (s j : ℕ) :
    let d := kmswWindowPatchData w s j
    KMSWWindowPatchRel (kmswStage w s) (kmswStage w (s + j))
      (kmswStage (fun i => w (s + i)) j) d.φ d.A d.B d.YL d.YR d.XL d.XR := by
  induction j with
  | zero => exact kmswWindowPatchRel_init w s
  | succ j ih =>
    have hh := patchStep_rel ih (kmswCodeStep (w (s + j)))
    rw [show s + (j + 1) = (s + j) + 1 from Nat.add_assoc s j 1]
    exact hh

private theorem patchStep_extends (G F : State) (c : Step) (d : KMSWWindowPatchData)
    (e : ℕ) (he : e < F.nextEdge) : (KMSWWindowPatchData.step G F c d).φ e = d.φ e := by
  cases c with
  | up => exact ite_eq_left he
  | down =>
    cases hu : F.UR with
    | cons q qs => simp only [KMSWWindowPatchData.step, hu]
    | nil => cases hb : d.B <;> simp only [KMSWWindowPatchData.step, hu, hb, ite_eq_left he]
  | left =>
    cases hs : F.UL.dropLast.reverse with
    | cons q qs => simp only [KMSWWindowPatchData.step, hs, ite_eq_left he]
    | nil => cases ha : d.A.reverse <;> simp only [KMSWWindowPatchData.step, hs, ha, ite_eq_left he]

 
theorem kmswWindowPatchData_extends (w : ℕ → Fin 3) (s j e : ℕ)
    (he : e < (kmswStage (fun i => w (s + i)) j).nextEdge) :
    (kmswWindowPatchData w s (j + 1)).φ e = (kmswWindowPatchData w s j).φ e :=
  patchStep_extends _ _ _ _ e he

 
theorem kmswWindowPatchData_extends_le (w : ℕ → Fin 3) (s j k : ℕ) (hjk : j ≤ k)
    (e : ℕ) (he : e < (kmswStage (fun i => w (s + i)) j).nextEdge) :
    (kmswWindowPatchData w s k).φ e = (kmswWindowPatchData w s j).φ e := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    rw [kmswWindowPatchData_extends w s k e
      (he.trans_le (kmswStage_nextEdge_mono _ hjk)), ih]

private def patchTriangle (F : State) : Step → List (ℕ × Bool)
  | .down => []
  | .up => [(F.active, false), (F.nextEdge + 1, true), (F.nextEdge, true)]
  | .left => match F.UL.dropLast.reverse with
    | e :: _ => [(e, false), (F.active, false), (F.nextEdge, true)]
    | [] => [(F.active, false), (F.nextEdge, true), (F.nextEdge + 1, false)]

private theorem patchStep_triangle {G₀ G : State} {u : ℕ → Fin 3} {j : ℕ}
    {d : KMSWWindowPatchData}
    (h : KMSWWindowPatchRel G₀ G (kmswStage u j) d.φ d.A d.B d.YL d.YR d.XL d.XR)
    (c : Step) (hc : c = .left ∨ c = .up) :
    List.IsRotated
      ((patchTriangle (kmswStage u j) c).map
        (fun p => ((d.step G (kmswStage u j) c).φ p.1, p.2)))
      (patchTriangle G c) := by
  let F := kmswStage u j
  have hf : F.active < F.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u j).1
  have hactive : d.φ F.active = G.active := h.active
  have hne : F.UL.map d.φ ≠ [] := by
    intro hz
    exact (kmswStage_UL_nonempty_active_last u j).1 (List.map_eq_nil_iff.mp hz)
  have hdrop : G.UL.dropLast.reverse = F.UL.dropLast.reverse.map d.φ ++ d.A.reverse := by
    rw [h.ul, List.dropLast_append_of_ne_nil hne, ← List.map_dropLast,
      List.reverse_append, List.map_reverse]
  change List.IsRotated
    ((patchTriangle F c).map (fun p => ((d.step G F c).φ p.1, p.2)))
    (patchTriangle G c)
  rcases hc with rfl | rfl
  · cases hs : F.UL.dropLast.reverse with
    | cons e es =>
      have he : e < F.nextEdge := by
        apply (kmswStage_boundary_ids_lt_nextEdge u j).2
        have hm : e ∈ F.UL := (List.dropLast_sublist _).subset
          (List.mem_reverse.mp (by rw [hs]; simp))
        simp only [List.mem_append]
        tauto
      have hg : G.UL.dropLast.reverse = d.φ e :: (es.map d.φ ++ d.A.reverse) := by
        rw [hdrop, hs, List.map_cons, List.cons_append]
      simp [patchTriangle, KMSWWindowPatchData.step, hs, hg, he, hf, hactive]
      exact List.IsRotated.refl _
    | nil =>
      cases ha : d.A.reverse with
      | nil =>
        have hg : G.UL.dropLast.reverse = [] := by
          rw [hdrop, hs, ha]; rfl
        simp [patchTriangle, KMSWWindowPatchData.step, hs, ha, hg, hf, hactive]
        exact List.IsRotated.refl _
      | cons q es =>
        have hg : G.UL.dropLast.reverse = q :: es := by
          rw [hdrop, hs, ha]; rfl
        simp only [patchTriangle, hs, hg, KMSWWindowPatchData.step, ha,
          List.map_cons, List.map_nil, ite_eq_left hf, hactive]
        refine ⟨2, ?_⟩
        simp
  · simp [patchTriangle, KMSWWindowPatchData.step, hf, hactive]
    exact List.IsRotated.refl _

private theorem patchTriangle_eq (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    patchTriangle (kmswStage w j.val) (kmswCodeStep (w j.val)) =
      stageTriangleDartList w j := by
  rcases j.property with h | h
  · simp only [kmswCodeStep, h, ite_true, patchTriangle,
      stageTriangleDartList, stageTriangleDartTriple]
    cases hs : (kmswStage w j.val).UL.dropLast.reverse <;> rfl
  · simp [kmswCodeStep, h, patchTriangle, stageTriangleDartList,
      stageTriangleDartTriple]

 
theorem kmswWindowPatchData_triangle_rotated (w : ℕ → Fin 3) (s m j : ℕ)
    (hj : j < m) (h : w (s + j) = 0 ∨ w (s + j) = 1) :
    List.IsRotated
      ((stageTriangleDartList (fun i => w (s + i)) ⟨j, h⟩).map
        (fun p => ((kmswWindowPatchData w s m).φ p.1, p.2)))
      (stageTriangleDartList w ⟨s + j, h⟩) := by
  let u := fun i => w (s + i)
  have hc : kmswCodeStep (u j) = .left ∨ kmswCodeStep (u j) = .up := by
    rcases h with h | h
    · exact Or.inl (by simp only [kmswCodeStep, show u j = 0 from h, ite_true])
    · exact Or.inr (by simp [kmswCodeStep, show u j = 1 from h])
  have hcreation := patchStep_triangle (kmswWindowPatchData_rel w s j)
    (kmswCodeStep (u j)) hc
  rw [patchTriangle_eq u ⟨j, h⟩, patchTriangle_eq w ⟨s + j, h⟩] at hcreation
  have hmaps :
      (stageTriangleDartList u ⟨j, h⟩).map
          (fun p => ((kmswWindowPatchData w s m).φ p.1, p.2)) =
        (stageTriangleDartList u ⟨j, h⟩).map
          (fun p => ((kmswWindowPatchData w s (j + 1)).φ p.1, p.2)) := by
    apply List.map_congr_left
    intro p hp
    have hbound : p.1 < (kmswStage u (j + 1)).nextEdge := by
      apply stage_face_dart_lt_nextEdge u (j + 1) p
      apply List.mem_append.mpr
      right
      exact List.mem_flatMap.mpr
        ⟨⟨j, h⟩, (mem_stageTriangleTimes u (j + 1) ⟨j, h⟩).mpr (Nat.lt_succ_self j), hp⟩
    exact congrArg (fun e => (e, p.2))
      (kmswWindowPatchData_extends_le w s (j + 1) m (by omega) p.1 hbound)
  rw [hmaps]
  exact hcreation

 
theorem kmswWindowPatchData_darts_mem (w : ℕ → Fin 3) (s m : ℕ) (p : ℕ × Bool)
    (hp : p ∈ stageTriangleDartsVal (fun i => w (s + i)) m) :
    ((kmswWindowPatchData w s m).φ p.1, p.2) ∈ stageTriangleDartsVal w (s + m) := by
  obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hp
  have ht' := (mem_stageTriangleTimes (fun i => w (s + i)) m t).mp ht
  have hr := kmswWindowPatchData_triangle_rotated w s m t.val ht' t.property
  apply List.mem_flatMap.mpr
  refine ⟨⟨s + t.val, t.property⟩, ?_, ?_⟩
  · apply (mem_stageTriangleTimes w (s + m) _).mpr
    change s + t.val < s + m
    omega
  · exact hr.mem_iff.mp (List.mem_map.mpr ⟨p, hpt, rfl⟩)

 
theorem kmswWindowPatchData_darts_injective (w : ℕ → Fin 3) (s m : ℕ) :
    Set.InjOn (fun p : ℕ × Bool => ((kmswWindowPatchData w s m).φ p.1, p.2))
      {p | p ∈ stageTriangleDartsVal (fun i => w (s + i)) m} := by
  intro p hp q hq heq
  have hpb := stage_face_dart_lt_nextEdge (fun i => w (s + i)) m p
    (List.mem_append.mpr (Or.inr hp))
  have hqb := stage_face_dart_lt_nextEdge (fun i => w (s + i)) m q
    (List.mem_append.mpr (Or.inr hq))
  have hside := congrArg Prod.snd heq
  exact Prod.ext
    ((kmswWindowPatchData_rel w s m).edge_injective p.1 hpb q.1 hqb
      (congrArg Prod.fst heq))
    hside

end DirectedDistances.KMSW
