module

public import DirectedDistances.KMSW.WholePlaneRightBoundaryRot

/-! Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem triangle_preimage (w : ℕ → Fin 3) (s m : ℕ)
    (g : StageDart (kmswStage w (s + m)).nextEdge)
    (j : TriangleCreationTime w) (hj : j.val < s + m) (hstart : s ≤ j.val)
    (hg : (g.1.val, g.2) ∈ stageTriangleDartList w j) :
    g ∈ Set.range (kmswWindowDartMap w s m) := by
  let u := fun i => w (s + i)
  let k := j.val - s
  have hk : j.val = s + k := by omega
  have hkm : k < m := by omega
  have hc : u k = 0 ∨ u k = 1 := by simpa only [u, hk] using j.property
  let jf : TriangleCreationTime u := ⟨k, hc⟩
  let jg : TriangleCreationTime w := ⟨s + k, hc⟩
  have hjg : j = jg := Subtype.ext hk
  have hmem : (g.1.val, g.2) ∈ stageTriangleDartList w jg := hjg ▸ hg
  have hr := kmswWindowPatchData_triangle_rotated w s m k hkm hc
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp (hr.mem_iff.mpr hmem)
  have hb : p.1 < (kmswStage u m).nextEdge := by
    apply stage_face_dart_lt_nextEdge u m p
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨jf, (mem_stageTriangleTimes u m jf).mpr hkm, hp⟩))
  refine ⟨(⟨p.1, hb⟩, p.2), ?_⟩
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst heq)
  · exact congrArg (fun z : ℕ × Bool => z.2) heq

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. Every finite ambient dart outside the window image is a prefix
dart, including darts of missing geometric edges. This asserts coverage, not order. -/
theorem kmswWindowDartMap_not_mem_range_lt_prefix (w : ℕ → Fin 3) (s m : ℕ)
    (g : StageDart (kmswStage w (s + m)).nextEdge)
    (hg : g ∉ Set.range (kmswWindowDartMap w s m)) :
    g.1.val < (kmswStage w s).nextEdge := by
  let u := fun i => w (s + i)
  let F := kmswStage u m
  let G₀ := kmswStage w s
  let G := kmswStage w (s + m)
  let data := kmswWindowPatchData w s m
  have hrel := kmswWindowPatchData_rel w s m
  change KMSWWindowPatchRel G₀ G F data.φ data.A data.B data.YL
    data.YR data.XL data.XR at hrel
  have oldbound (e : ℕ) (he : e ∈ G₀.UL ++ G₀.UR ++ G₀.LL ++ G₀.LR) :
      e < G₀.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w s).2 e he
  have mapped (e : ℕ) (he : e < F.nextEdge) (heq : data.φ e = g.1.val) : False := by
    apply hg
    exact ⟨(⟨e, he⟩, g.2), Prod.ext (Fin.ext heq) rfl⟩
  have bnd (e : ℕ) (he : e ∈ F.UL ++ F.UR ++ F.LL ++ F.LR) :
      e < F.nextEdge := (kmswStage_boundary_ids_lt_nextEdge u m).2 e he
  rcases stage_dart_partition w (s + m) g with hout | ⟨j, ⟨hj, hgj⟩, _⟩
  · rcases (stageOuterWord_mem_iff w (s + m) g).mp hout with
      ⟨_, hUL | hUR⟩ | ⟨_, hLR | hLL⟩
    · rw [hrel.ul] at hUL
      rcases List.mem_append.mp hUL with hA | hm
      · have hdrop : g.1.val ∈ G₀.UL.dropLast := by
          rw [hrel.left_residual]
          exact List.mem_append_left _ hA
        apply oldbound
        have hUL := List.dropLast_subset _ hdrop
        simp only [List.mem_append]
        tauto
      · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
        apply False.elim
        apply mapped e (bnd e ?_) heq
        simp only [List.mem_append]
        tauto
    · rw [hrel.ur] at hUR
      rcases List.mem_append.mp hUR with hm | hB
      · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
        apply False.elim
        apply mapped e (bnd e ?_) heq
        simp only [List.mem_append]
        tauto
      · have hUR : g.1.val ∈ G₀.UR := by
          rw [hrel.right_residual]
          exact List.mem_append_right _ hB
        apply oldbound
        simp only [List.mem_append]
        tauto
    · rw [hrel.lr] at hLR
      rcases List.mem_append.mp hLR with ho | hm
      · apply oldbound
        simp only [List.mem_append]
        tauto
      · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
        have heF : e ∈ F.LR := by
          rw [hrel.lr_split]
          exact List.mem_append_right _ he
        apply False.elim
        apply mapped e (bnd e ?_) heq
        simp only [List.mem_append]
        tauto
    · rw [hrel.ll] at hLL
      rcases List.mem_append.mp hLL with hm | ho
      · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
        have heF : e ∈ F.LL := by
          rw [hrel.ll_split]
          exact List.mem_append_left _ he
        apply False.elim
        apply mapped e (bnd e ?_) heq
        simp only [List.mem_append]
        tauto
      · apply oldbound
        simp only [List.mem_append]
        tauto
  · by_cases hold : j.val < s
    · apply stage_face_dart_lt_nextEdge w s (g.1.val, g.2)
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨j, (mem_stageTriangleTimes w s j).mpr hold, hgj⟩))
    · exact (hg (triangle_preimage w s m g j hj (by omega) hgj)).elim

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. The infinite window omits only prefix geometric darts. -/
theorem wholePlaneDartTrans_not_mem_range_lt_prefix (W : ℤ → Fin 3)
    (N M : ℕ) (hNM : N ≤ M) (g : ℕ × Bool)
    (hg : g ∉ Set.range (wholePlaneDartTrans W N M hNM)) :
    g.1 < (kmswStage (shiftedStream W M) (M - N)).nextEdge := by
  let w := shiftedStream W M
  let s := M - N
  let m := g.1
  have hb : g.1 < (kmswStage w (s + m)).nextEdge :=
    (kmsw_edge_allocated_by_self w g.1).trans_le
      (kmswStage_nextEdge_mono w (by omega))
  let x : StageDart (kmswStage w (s + m)).nextEdge := (⟨g.1, hb⟩, g.2)
  apply kmswWindowDartMap_not_mem_range_lt_prefix w s m x
  rintro ⟨d, hd⟩
  apply hg
  refine ⟨(d.1.val, d.2), ?_⟩
  apply Prod.ext
  · change kmswWindowEdgeMapInf w s d.1.val = g.1
    rw [kmswWindowEdgeMapInf_eq_stage w s m d.1.val d.1.isLt]
    exact congrArg (fun z => z.1.val) hd
  · exact congrArg (fun z : StageDart (kmswStage w (s + m)).nextEdge => z.2) hd

private def dartValue {k : ℕ} (d : StageDart k) : ℕ × Bool := (d.1.val, d.2)

private def dartBase (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private theorem stage_base (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) d = dartBase w (dartValue d) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;> simp only [stageEndpoint, dartBase, dartValue, hb,
    Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem symm_stage_base (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) ((stageRot w n).symm d) =
      stageEndpoint (kmswStage w n) d := by
  exact (stageRot_sameCycle_iff_endpoint_eq w n _ _).mp
    ⟨1, (stageRot w n).apply_symm_apply d⟩

private theorem symm_stage_pow_base (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (k : ℕ) :
    stageEndpoint (kmswStage w n) (((stageRot w n).symm ^ k) d) =
      stageEndpoint (kmswStage w n) d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, symm_stage_base, ih]

private theorem complete_exists (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (v : ℕ) : ∃ n, kmswVertexComplete w n v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hm : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)} :=
    ⟨e, kmsw_edge_allocated_by_self w e, he⟩
  exact (hB hm).trans_lt (kmsw_edge_allocated_by_self w B)

private theorem symm_pow_eq_stage (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) d)) (k : ℕ) :
    ((kmswInfRot w hfin).symm ^ k) (dartValue d) =
      dartValue (((stageRot w n).symm ^ k) d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    exact kmswInfRot_symm_eq_stage w hfin n _ (by rw [symm_stage_pow_base]; exact hc)

private theorem symm_periodic (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) : ∃ k : ℕ, 0 < k ∧ ((kmswInfRot w hfin).symm ^ k) d = d := by
  obtain ⟨n, hn⟩ := complete_exists w hfin (dartBase w d)
  let m := max n d.1
  have hb : d.1 < (kmswStage w m).nextEdge :=
    (kmsw_edge_allocated_by_self w d.1).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_max_right _ _))
  let x : StageDart (kmswStage w m).nextEdge := (⟨d.1, hb⟩, d.2)
  have hc : kmswVertexComplete w m (stageEndpoint (kmswStage w m) x) := by
    rw [stage_base]
    intro e he
    exact (hn e he).trans_le (kmswStage_nextEdge_mono w (Nat.le_max_left _ _))
  obtain ⟨k, hk, _, he⟩ :=
    (Equiv.Perm.SameCycle.refl (stageRot w m).symm x).exists_pow_eq''
  refine ⟨k, hk, ?_⟩
  change ((kmswInfRot w hfin).symm ^ k) (dartValue x) = dartValue x
  rw [symm_pow_eq_stage w hfin m x hc k, he]

private theorem symm_pow_base (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) (k : ℕ) :
    dartBase w (((kmswInfRot w hfin).symm ^ k) d) = dartBase w d := by
  have step (z : ℕ × Bool) : dartBase w ((kmswInfRot w hfin).symm z) =
      dartBase w z := by
    obtain ⟨n, hn⟩ := kmswInfRot_symm_eventually_eq_stage w hfin z
    obtain ⟨hz, he⟩ := hn n le_rfl
    let x : StageDart (kmswStage w n).nextEdge := (⟨z.1, hz⟩, z.2)
    rw [he]
    exact (stage_base w n _).symm.trans
      ((symm_stage_base w n x).trans (stage_base w n x))
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, step, ih]

private theorem trans_base (W : ℤ → Fin 3) (N M : ℕ) (hNM : N ≤ M)
    (d : ℕ × Bool) :
    dartBase (shiftedStream W M) (wholePlaneDartTrans W N M hNM d) =
      wholePlaneVertexTrans W N M hNM (dartBase (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [dartBase, wholePlaneDartTrans, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeTrans_west W N M hNM d.1
  · exact wholePlaneEdgeTrans_east W N M hNM d.1

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. A dart at an image vertex outside the run image forces that
vertex onto the prefix seam. No edge-presence or directed-edge orientation hypothesis
is imposed on `g`. -/
theorem wholePlaneDartTrans_not_mem_range_not_fresh (W : ℤ → Fin 3)
    (N M : ℕ) (hNM : N ≤ M) (v : ℕ) (g : ℕ × Bool)
    (hg : g ∉ Set.range (wholePlaneDartTrans W N M hNM))
    (hv : (if g.2 then edgeEast (shiftedStream W M) g.1
      else edgeWest (shiftedStream W M) g.1) = wholePlaneVertexTrans W N M hNM v) :
    ¬ wholePlaneFresh W N M hNM v := by
  have he := wholePlaneDartTrans_not_mem_range_lt_prefix W N M hNM g hg
  have hb := kmswStage_endpoints_lt_nextVertex (shiftedStream W M) (M - N) g.1 he
  have hend := edge_endpoints_eq (shiftedStream W M) he
  have hlt : (if g.2 then edgeEast (shiftedStream W M) g.1
      else edgeWest (shiftedStream W M) g.1) <
      (kmswStage (shiftedStream W M) (M - N)).nextVertex := by
    cases hs : g.2
    · simpa only [hs, Bool.false_eq_true, ↓reduceIte, hend.1] using hb.1
    · simpa only [hs, ↓reduceIte, hend.2] using hb.2
  rw [hv] at hlt
  exact Nat.not_le_of_gt hlt





theorem wholePlaneInfRot_symm_firstReturn_exists (W : ℤ → Fin 3)
    (N M : ℕ) (hNM : N ≤ M) (hM : KMSWFiniteIncidence (shiftedStream W M))
    (d : ℕ × Bool) :
    ∃ (k : ℕ) (e : ℕ × Bool), 0 < k ∧
      (if e.2 then edgeEast (shiftedStream W N) e.1
        else edgeWest (shiftedStream W N) e.1) =
        (if d.2 then edgeEast (shiftedStream W N) d.1
          else edgeWest (shiftedStream W N) d.1) ∧
      ((kmswInfRot (shiftedStream W M) hM).symm ^ k)
        (wholePlaneDartTrans W N M hNM d) = wholePlaneDartTrans W N M hNM e ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswInfRot (shiftedStream W M) hM).symm ^ j)
          (wholePlaneDartTrans W N M hNM d) ∉
            Set.range (wholePlaneDartTrans W N M hNM) ∧
        (((kmswInfRot (shiftedStream W M) hM).symm ^ j)
          (wholePlaneDartTrans W N M hNM d)).1 <
            (kmswStage (shiftedStream W M) (M - N)).nextEdge := by
  classical
  let I := wholePlaneDartTrans W N M hNM
  let ρ := (kmswInfRot (shiftedStream W M) hM).symm
  obtain ⟨n, hn, hret⟩ := symm_periodic (shiftedStream W M) hM (I d)
  have hex : ∃ k : ℕ, 0 < k ∧ (ρ ^ k) (I d) ∈ Set.range I :=
    ⟨n, hn, d, hret.symm⟩
  let k := Nat.find hex
  obtain ⟨hk, e, he⟩ := Nat.find_spec hex
  have hgap : ∀ j : ℕ, 0 < j → j < k → (ρ ^ j) (I d) ∉ Set.range I := by
    intro j hj hjk hmem
    exact Nat.find_min hex hjk ⟨hj, hmem⟩
  refine ⟨k, e, hk, ?_, he.symm, fun j hj hjk => ⟨hgap j hj hjk, ?_⟩⟩
  · apply wholePlaneVertexTrans_injective W N M hNM
    change wholePlaneVertexTrans W N M hNM (dartBase (shiftedStream W N) e) =
      wholePlaneVertexTrans W N M hNM (dartBase (shiftedStream W N) d)
    rw [← trans_base, ← trans_base]
    change dartBase (shiftedStream W M) (I e) = dartBase (shiftedStream W M) (I d)
    rw [he]
    exact symm_pow_base (shiftedStream W M) hM (I d) k
  · exact wholePlaneDartTrans_not_mem_range_lt_prefix W N M hNM _ (hgap j hj hjk)

end DirectedDistances.KMSW
