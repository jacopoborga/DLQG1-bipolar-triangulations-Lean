module

public import DirectedDistances.PlanarMap.PlanarPathGlueGeodesic
public import DirectedDistances.PlanarMap.PlanarPathGlueBasePackage
public import DirectedDistances.PlanarMap.PlanarPathCutLeftmostBridge
public import DirectedDistances.PlanarMap.LRIndClassPredicates

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PlanarMap

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)



@[expose] noncomputable def glueSeamPathBase :
    SimpleDirectedDartPath (glueBase BL BR).map
      (glueBase BL BR).source (glueBase BL BR).sink s :=
  glueSeamPath BL BR

 
theorem glueSeamPathBase_darts :
    (glueSeamPathBase BL BR).darts =
      BL.rightPath.darts.map (fun d => glueIdentify BL BR (.inl d)) :=
  glueSeamPath_darts BL BR



theorem glueSeamPathBase_isXDPGeodesic (x : XDP)
    (hL : IsXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) :
    IsXDPGeodesicBase (glueBase BL BR) x (glueSeamPathBase BL BR) := by
  cases x with
  | ldp =>
    intro k Q
    exact (glueSeamPath_extremal_length BL BR .ldp hL hR).2 ⟨Q⟩
  | sdp =>
    intro k Q
    exact (glueSeamPath_extremal_length BL BR .sdp hL hR).2 ⟨Q⟩



theorem glue_xdpLength (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) :
    xdpLengthBase (glueBase BL BR) x = s := by
  have h := glueSeamPathBase_isXDPGeodesic BL BR x hL.1 hR
  cases x with
  | ldp =>
    exact ((isLDPGeodesicBase_iff_length_eq (glueBase BL BR)
      (glueSeamPathBase BL BR)).mp h).symm
  | sdp =>
    exact ((isSDPGeodesicBase_iff_length_eq (glueBase BL BR)
      (glueSeamPathBase BL BR)).mp h).symm



theorem glue_geodesic_seam_visit_index (x : XDP)
    (hL : IsXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) {n : ℕ}
    (Q : SimpleDirectedDartPath (glueBase BL BR).map
      (glueBase BL BR).source (glueBase BL BR).sink n)
    (hQ : IsXDPGeodesicBase (glueBase BL BR) x Q)
    (a : Fin (n + 1)) (i : Fin (s + 1))
    (hi : Q.vertices.get ⟨a.val, by rw [Q.vertices_length]; exact a.isLt⟩ =
      (glueSeamPathBase BL BR).vertices.get
        ⟨i.val, by rw [(glueSeamPathBase BL BR).vertices_length]; exact i.isLt⟩) :
    a.val = i.val := by
  have hqa := xdpGeodesic_prefix_suffix_distanceNat (glueBase BL BR) x Q hQ a
  have hpi := xdpGeodesic_prefix_suffix_distanceNat (glueBase BL BR) x
    (glueSeamPathBase BL BR) (glueSeamPathBase_isXDPGeodesic BL BR x hL hR) i
  cases x <;> dsimp only at hqa hpi <;> rw [hi] at hqa <;>
    exact hqa.1.symm.trans hpi.1




theorem glue_geodesic_segment_tight (x : XDP)
    (hL : IsXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) {n : ℕ}
    (Q : SimpleDirectedDartPath (glueBase BL BR).map
      (glueBase BL BR).source (glueBase BL BR).sink n)
    (hQ : IsXDPGeodesicBase (glueBase BL BR) x Q)
    (a b : Fin (n + 1)) (i j : Fin (s + 1))
    (hi : Q.vertices.get ⟨a.val, by rw [Q.vertices_length]; exact a.isLt⟩ =
      (glueSeamPathBase BL BR).vertices.get
        ⟨i.val, by rw [(glueSeamPathBase BL BR).vertices_length]; exact i.isLt⟩)
    (hj : Q.vertices.get ⟨b.val, by rw [Q.vertices_length]; exact b.isLt⟩ =
      (glueSeamPathBase BL BR).vertices.get
        ⟨j.val, by rw [(glueSeamPathBase BL BR).vertices_length]; exact j.isLt⟩) :
    b.val - a.val = j.val - i.val := by
  rw [glue_geodesic_seam_visit_index BL BR x hL hR Q hQ a i hi,
    glue_geodesic_seam_visit_index BL BR x hL hR Q hQ b j hj]




theorem glue_left_tightSegment_eq (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (i j : Fin (s + 1)) (hij : i.val ≤ j.val) {k : ℕ}
    (T : SimpleDirectedDartPath BL.map
      (BL.rightPath.vertices.get ⟨i.val, by rw [BL.rightPath.vertices_length]; exact i.isLt⟩)
      (BL.rightPath.vertices.get ⟨j.val, by rw [BL.rightPath.vertices_length]; exact j.isLt⟩) k)
    (hk : k = j.val - i.val) :
    T.darts = (BL.rightPath.darts.drop i.val).take (j.val - i.val) := by
  let R := ((BL.rightPath.prefix i).appendAcyclic BL.map BL.acyclic T).appendAcyclic
    BL.map BL.acyclic (BL.rightPath.suffix j)
  have hlen : i.val + k + (s - j.val) = s := by have := j.isLt; omega
  have hR : IsXDPGeodesicBase BL x R := by
    cases x with
    | ldp => intro m U; have h := hL.1 U; omega
    | sdp => intro m U; have h := hL.1 U; omega
  have hd := hL.2 R hR
  have hRd : R.darts = BL.rightPath.darts.take i.val ++ T.darts ++
      BL.rightPath.darts.drop j.val := by
    simp only [R, SimpleDirectedDartPath.appendAcyclic_darts,
      SimpleDirectedDartPath.prefix_darts, SimpleDirectedDartPath.suffix_darts]
  have htake : (BL.rightPath.darts.take i.val).length = i.val := by
    simp only [List.length_take, BL.rightPath.darts_length,
      Nat.min_eq_left (by have := i.isLt; omega : i.val ≤ s)]
  have he := congrArg (fun ds : List DL => (ds.drop i.val).take k) hd
  rw [hRd, List.append_assoc] at he
  have hdrop : (BL.rightPath.darts.take i.val).drop i.val = [] := by
    apply List.drop_eq_nil_of_le
    omega
  rw [List.drop_append, hdrop, htake] at he
  have htakeT : T.darts.take k = T.darts := by
    apply List.take_of_length_le
    exact Nat.le_of_eq T.darts_length
  simpa only [Nat.sub_self, List.drop_zero, List.nil_append,
    List.take_append, T.darts_length, htakeT, List.take_zero,
    List.append_nil] using he.trans (congrArg (fun m => (BL.rightPath.darts.drop i.val).take m) hk)

private abbrev vertexAt {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {u v : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M u v n) (i : Fin (n + 1)) :=
  P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩

private theorem seam_vertex (i : Fin (s + 1)) :
    vertexAt (glueSeamPathBase BL BR) i =
      glueDirectedVertexMap BL BR (.inl (vertexAt BL.rightPath i)) := by
  change (BL.rightPath.vertices.map (fun v => glueDirectedVertexMap BL BR (.inl v))).get _ = _
  exact List.getElem_map _

private theorem directed_vertex_eq (v w : MapVertex BL.map ⊕ MapVertex BR.map) :
    glueDirectedVertexMap BL BR v = glueDirectedVertexMap BL BR w ↔
      glueVertexMap BL BR v = glueVertexMap BL BR w := by
  cases v <;> cases w <;> rename_i v w
  all_goals
    refine Quotient.inductionOn₂ v w ?_
    intro d e
    change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
    rw [Quotient.eq, Quotient.eq]
    change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
    rw [glueDirectedMap_toCombinatorialMap]
    rfl

private theorem left_injective :
    Function.Injective (fun v : MapVertex BL.map => glueDirectedVertexMap BL BR (.inl v)) :=
  fun _ _ h => glueVertexMap_left_injective BL BR ((directed_vertex_eq BL BR _ _).mp h)

private theorem cross (u : MapVertex BL.map) (v : MapVertex BR.map)
    (h : glueDirectedVertexMap BL BR (.inl u) = glueDirectedVertexMap BL BR (.inr v)) :
    ∃ i : Fin (s + 1), u = vertexAt BL.rightPath i ∧ v = vertexAt BR.leftPath i := by
  obtain ⟨i, hi, hj⟩ := (glueVertexMap_cross_iff BL BR u v).mp
    ((directed_vertex_eq BL BR _ _).mp h)
  exact ⟨i, hi.trans (glueLeftSeamVertexDart_vertex BL i),
    hj.trans (glueRightSeamVertexDart_vertex BR i)⟩

private theorem left_head (d : DL) :
    dartHeadVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inl d)) =
      glueDirectedVertexMap BL BR (.inl (dartHeadVertex BL.map d)) := by
  change dartTailVertex (glueDirectedMap BL BR)
    ((glueDirectedMap BL BR).toCombinatorialMap.edgeInv (glueIdentify BL BR (.inl d))) = _
  rw [glueDirectedMap_toCombinatorialMap, glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl

private def zeroPath {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (u : MapVertex M) : SimpleDirectedDartPath M u u 0 where
  darts := []
  vertices := [u]
  darts_length := rfl
  vertices_length := rfl
  vertices_nodup := by simp only [List.nodup_singleton]
  start_vertex := rfl
  end_vertex := rfl
  edge_step := by intro i; exact Fin.elim0 i

private def onePath (d : DL) (ht : BL.map.tail d) :
    SimpleDirectedDartPath BL.map (dartTailVertex BL.map d) (dartHeadVertex BL.map d) 1 where
  darts := [d]
  vertices := [dartTailVertex BL.map d, dartHeadVertex BL.map d]
  darts_length := rfl
  vertices_length := rfl
  vertices_nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true, or_false]
    intro h
    exact BL.acyclic _ (Relation.TransGen.single
      ⟨d, BL.noMissingDarts d, ht, rfl, h.symm⟩)
  start_vertex := rfl
  end_vertex := rfl
  edge_step := by
    intro i
    have hi0 : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
    have hi : i = ⟨0, by simp⟩ := Fin.ext hi0
    subst i
    exact ⟨BL.noMissingDarts d, ht, rfl, rfl⟩

private theorem left_lift_to_seam
    (Q : SimpleDirectedDartPath (glueDirectedMap BL BR)
      (glueDirectedVertexMap BL BR (.inl BL.source))
      (glueDirectedVertexMap BL BR (.inl BL.sink)) s)
    (a : Fin (s + 1)) (u : MapVertex BL.map)
    (hu : glueDirectedVertexMap BL BR (.inl u) = vertexAt Q a) :
    ∃ (b : Fin (s + 1)) (j : Fin (s + 1)), a.val ≤ b.val ∧
      vertexAt Q b = vertexAt (glueSeamPathBase BL BR) j ∧
      Nonempty (SimpleDirectedDartPath BL.map u (vertexAt BL.rightPath j) (b.val - a.val)) := by
  classical
  generalize hn : s - a.val = remaining
  induction remaining using Nat.strong_induction_on generalizing a u with
  | h remaining ih =>
    by_cases hseam : ∃ j : Fin (s + 1), u = vertexAt BL.rightPath j
    · obtain ⟨j, rfl⟩ := hseam
      refine ⟨a, j, le_refl _, hu.symm.trans (seam_vertex BL BR j).symm, ?_⟩
      simpa only [Nat.sub_self] using (show Nonempty (SimpleDirectedDartPath BL.map
        (vertexAt BL.rightPath j) (vertexAt BL.rightPath j) 0) from ⟨zeroPath BL.map _⟩)
    · have has : a.val < s := by
        by_contra hnot
        have ha : a.val = s := by have := a.isLt; omega
        have he : vertexAt Q a = glueDirectedVertexMap BL BR (.inl BL.sink) := by
          simpa only [vertexAt, ha] using Q.end_vertex
        have he' : u = BL.sink := left_injective BL BR (hu.trans he)
        apply hseam
        exact ⟨⟨s, by omega⟩, he'.trans BL.rightPath.end_vertex.symm⟩
      let da : Fin Q.darts.length := ⟨a.val, by rw [Q.darts_length]; exact has⟩
      have hs := Q.edge_step da
      dsimp only [da] at hs
      cases hd : Q.darts.get da with
      | inr d =>
        have hdv : glueDirectedVertexMap BL BR (.inl u) =
            glueDirectedVertexMap BL BR (.inr (dartTailVertex BR.map d.val)) := by
          calc
            _ = vertexAt Q a := hu
            _ = dartTailVertex (glueDirectedMap BL BR) (.inr d) := by simpa only [vertexAt, da, hd] using hs.2.2.1
            _ = _ := by rw [← glueIdentify_inr_kept BL BR d]; rfl
        obtain ⟨j, hj, _⟩ := cross BL BR _ _ hdv
        exact False.elim (hseam ⟨j, hj⟩)
      | inl d =>
        have ht : BL.map.tail d.val := by
          have h := hs.2.1
          rw [hd] at h
          exact (glueDirectedMap_tail BL BR (.inl d)).mp h
        have htail : u = dartTailVertex BL.map d.val := by
          apply left_injective BL BR
          calc
            _ = vertexAt Q a := hu
            _ = dartTailVertex (glueDirectedMap BL BR) (.inl d) := by simpa only [vertexAt, da, hd] using hs.2.2.1
            _ = _ := by rw [← glueIdentify_inl_kept BL BR d]; rfl
        have hhead : glueDirectedVertexMap BL BR (.inl (dartHeadVertex BL.map d.val)) =
            vertexAt Q ⟨a.val + 1, by omega⟩ := by
          rw [← left_head BL BR, glueIdentify_inl_kept BL BR d]
          simpa only [vertexAt, da, hd] using hs.2.2.2.symm
        obtain ⟨b, j, hab, hb, ⟨T⟩⟩ := ih (s - (a.val + 1)) (by omega)
          ⟨a.val + 1, by omega⟩ (dartHeadVertex BL.map d.val) hhead rfl
        subst u
        let R := (onePath BL d.val ht).appendAcyclic BL.map BL.acyclic T
        have hlen : 1 + (b.val - (a.val + 1)) = b.val - a.val := by
          change a.val + 1 ≤ b.val at hab
          omega
        refine ⟨b, j, by omega, hb, ?_⟩
        exact ⟨hlen ▸ R⟩




theorem glue_geodesic_seam_departure_right (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath)
    (Q : SimpleDirectedDartPath (glueDirectedMap BL BR)
      (glueDirectedVertexMap BL BR (.inl BL.source))
      (glueDirectedVertexMap BL BR (.inl BL.sink)) s)
    (hQ : IsXDPGeodesicBase (glueBase BL BR) x Q) (i : Fin s)
    (hv : Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ =
      (glueSeamPathBase BL BR).vertices.get
        ⟨i.val, by rw [(glueSeamPathBase BL BR).vertices_length]; omega⟩)
    (hdiff : Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩ ≠
      (glueSeamPathBase BL BR).darts.get
        ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩) :
    ∃ d : DR, BR.map.tail d ∧
      dartTailVertex BR.map d = BR.leftPath.vertices.get
        ⟨i.val, by rw [BR.leftPath.vertices_length]; omega⟩ ∧
      d ∉ BR.leftPath.darts ∧
      glueIdentify BL BR (.inr d) = Q.darts.get
        ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩ := by
  let qi : Fin Q.darts.length := ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩
  have hs := Q.edge_step qi
  dsimp only [qi] at hs
  cases hd : Q.darts.get qi with
  | inr d =>
    have ht : BR.map.tail d.val := by
      have h := hs.2.1
      rw [show Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩ = .inr d from hd] at h
      exact (glueDirectedMap_tail BL BR (.inr d)).mp h
    have hc : glueDirectedVertexMap BL BR (.inl (vertexAt BL.rightPath ⟨i.val, by omega⟩)) =
        glueDirectedVertexMap BL BR (.inr (dartTailVertex BR.map d.val)) := by
      calc
        _ = vertexAt Q ⟨i.val, by omega⟩ := (seam_vertex BL BR _).symm.trans hv.symm
        _ = dartTailVertex (glueDirectedMap BL BR) (.inr d) := by simpa only [vertexAt, qi, hd] using hs.2.2.1
        _ = _ := by rw [← glueIdentify_inr_kept BL BR d]; rfl
    obtain ⟨j, hj, hdj⟩ := cross BL BR _ _ hc
    have hij : (⟨i.val, by omega⟩ : Fin (s + 1)) = j := by
      apply Fin.ext
      exact congrArg (fun k : Fin BL.rightPath.vertices.length => k.val)
        (BL.rightPath.vertices_nodup.get_inj_iff.mp hj)
    subst j
    exact ⟨d.val, ht, hdj, d.property, glueIdentify_inr_kept BL BR d⟩
  | inl d =>
    have ht : BL.map.tail d.val := by
      have h := hs.2.1
      rw [show Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩ = .inl d from hd] at h
      exact (glueDirectedMap_tail BL BR (.inl d)).mp h
    have htail : dartTailVertex BL.map d.val = vertexAt BL.rightPath ⟨i.val, by omega⟩ := by
      apply left_injective BL BR
      calc
        _ = dartTailVertex (glueDirectedMap BL BR) (.inl d) := by rw [← glueIdentify_inl_kept BL BR d]; rfl
        _ = vertexAt Q ⟨i.val, by omega⟩ := by simpa only [vertexAt, qi, hd] using hs.2.2.1.symm
        _ = _ := hv.trans (seam_vertex BL BR ⟨i.val, by omega⟩)
    have hhead : glueDirectedVertexMap BL BR (.inl (dartHeadVertex BL.map d.val)) =
        vertexAt Q ⟨i.val + 1, by omega⟩ := by
      rw [← left_head BL BR, glueIdentify_inl_kept BL BR d]
      simpa only [vertexAt, qi, hd] using hs.2.2.2.symm
    obtain ⟨b, j, hab, hb, ⟨T⟩⟩ := left_lift_to_seam BL BR Q
      ⟨i.val + 1, by omega⟩ (dartHeadVertex BL.map d.val) hhead
    have hbj := glue_geodesic_seam_visit_index BL BR x hL.1 hR Q hQ b j hb
    change i.val + 1 ≤ b.val at hab
    have hij : i.val ≤ j.val := by omega
    let R := (onePath BL d.val ht).appendAcyclic BL.map BL.acyclic T
    let R' : SimpleDirectedDartPath BL.map
        (vertexAt BL.rightPath ⟨i.val, by omega⟩) (vertexAt BL.rightPath j)
        (1 + (b.val - (i.val + 1))) := { R with start_vertex := R.start_vertex.trans htail }
    have he := glue_left_tightSegment_eq BL x hL ⟨i.val, by omega⟩ j hij R' (by change 1 + (b.val - (i.val + 1)) = j.val - i.val; omega)
    have hlen : 0 < j.val - i.val := by omega
    have h0 := List.getElem_of_eq he (i := 0) (by
      rw [R'.darts_length]
      omega)
    have hdseam : d.val = BL.rightPath.darts.get
        ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩ := by
      simpa only [R', R, SimpleDirectedDartPath.appendAcyclic_darts, onePath,
        List.getElem_append_left (by simp : 0 < [d.val].length), List.getElem_cons_zero,
        List.getElem_take, List.getElem_drop, Nat.add_zero, List.get_eq_getElem] using h0
    apply False.elim
    apply hdiff
    change Q.darts.get qi = _
    rw [hd, ← glueIdentify_inl_kept BL BR d, hdseam]
    change glueIdentify BL BR (.inl _) =
      (BL.rightPath.darts.map (fun e => glueIdentify BL BR (.inl e))).get _
    exact (List.getElem_map (fun e => glueIdentify BL BR (.inl e))
      (l := BL.rightPath.darts) (i := i.val)).symm

private theorem left_tail (d : DL) (ht : BL.map.tail d) :
    (glueDirectedMap BL BR).tail (glueIdentify BL BR (.inl d)) := by
  have hd : BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts := by
    intro hm
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    exact (BL.map.tail_iff d (BL.noMissingDarts d)).mp ht
      (hj ▸ (BL.rightPath.edge_step j).2.1)
  rw [glueIdentify_inl_kept BL BR ⟨d, hd⟩, glueDirectedMap_tail]
  exact ht

private theorem left_tail_iff (d : DL) :
    (glueDirectedMap BL BR).tail (glueIdentify BL BR (.inl d)) ↔ BL.map.tail d := by
  constructor
  · intro ht
    by_contra hn
    have hflip : BL.map.tail (BL.map.toCombinatorialMap.edgeInv d) := by
      apply (BL.map.tail_iff _ (BL.noMissingDarts _)).mpr
      simpa only [BL.map.toCombinatorialMap.edgeInv_invol] using hn
    have hg := left_tail BL BR _ hflip
    have hnot := ((glueDirectedMap BL BR).tail_iff _
      (glueDirectedMap_noMissing BL BR _)).mp ht
    apply hnot
    rw [glueDirectedMap_toCombinatorialMap, glueCombinatorialMap_edgeInv,
      glueEdgeInv_identify]
    exact hg
  · exact left_tail BL BR d

private theorem outgoing_outer_mem_left {D : Type*} [Fintype D] [DecidableEq D]
    {a b : ℕ} (B : BipolarTriangulationWithBoundaryBase D a b)
    (d : D) (ht : B.map.tail d) (ho : B.map.IsOuter d) : d ∈ B.leftPath.darts := by
  rcases (isOuter_iff_mem_outerArcs B d).mp ho with hl | hr
  · exact (mem_pathCutLeftOuterArc_iff B d).mp hl
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ((mem_pathCutRightOuterArc_iff B d).mp hr)
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (List.mem_reverse.mp he)
    exact False.elim (((B.map.tail_iff e (B.noMissingDarts e)).mp
      (hj ▸ (B.rightPath.edge_step j).2.1)) ht)

private theorem mem_left_eq_leftmost {D : Type*} [Fintype D] [DecidableEq D]
    {a b : ℕ} (B : BipolarTriangulationWithBoundaryBase D a b)
    (d : D) (hd : d ∈ B.leftPath.darts) (v : MapVertex B.map)
    (hv : dartTailVertex B.map d = v) (hvs : v ≠ B.sink) :
    d = leftmostOutgoing B v hvs := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
  have hjlt : j.val < a := by have := j.isLt; have := B.leftPath.darts_length; omega
  have he := leftPath_edge_eq_leftmostOutgoing B j.val hjlt
  have hvj : vertexAt B.leftPath ⟨j.val, by omega⟩ = v :=
    (B.leftPath.edge_step j).2.2.1.trans (hj ▸ hv)
  rw [show B.leftPath.darts.get ⟨j.val, j.isLt⟩ = d from hj] at he
  simpa only [← hvj] using he

private theorem seam_eq_leftmost_of_no_left (i : Fin s)
    (hno : ¬ ∃ e : DL, BL.map.tail e ∧
      dartTailVertex BL.map e = vertexAt BL.rightPath ⟨i.val, by omega⟩ ∧
      e ∉ BL.rightPath.darts)
    (hvs : vertexAt (glueSeamPathBase BL BR) ⟨i.val, by omega⟩ ≠ (glueBase BL BR).sink) :
    (glueSeamPathBase BL BR).darts.get
      ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩ =
      leftmostOutgoing (glueBase BL BR)
        (vertexAt (glueSeamPathBase BL BR) ⟨i.val, by omega⟩) hvs := by
  classical
  let v := vertexAt BL.rightPath ⟨i.val, by omega⟩
  let e := BL.rightPath.darts.get ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩
  have he : BL.map.tail e := (BL.rightPath.edge_step _).2.1
  have hev : dartTailVertex BL.map e = v := (BL.rightPath.edge_step _).2.2.1.symm
  have hvt : v ≠ BL.sink := simplePath_vertex_ne_end BL.rightPath i.val i.isLt
  let c := leftmostOutgoing BL v hvt
  have hc := canonicalLeftmostOutgoing_spec BL v hvt
  have hcmem : c ∈ BL.rightPath.darts := by
    by_contra h
    exact hno ⟨c, hc.2, hc.1, h⟩
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hcmem
  have hji : j.val = i.val := by
    have hcv : dartTailVertex BL.map c = v := hc.1
    have hvj := (BL.rightPath.edge_step j).2.2.1.trans
      ((congrArg (dartTailVertex BL.map) hj).trans hcv)
    exact congrArg (fun k : Fin BL.rightPath.vertices.length => k.val)
      (BL.rightPath.vertices_nodup.get_inj_iff.mp hvj)
  have hce : c = e := by
    calc
      c = BL.rightPath.darts.get j := hj.symm
      _ = e := congrArg BL.rightPath.darts.get (Fin.ext hji)
  have hse : (glueSeamPathBase BL BR).darts.get
      ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩ =
      glueIdentify BL BR (.inl e) := List.getElem_map _
  rw [hse]
  have hgv : dartTailVertex (glueBase BL BR).map (glueIdentify BL BR (.inl e)) =
      vertexAt (glueSeamPathBase BL BR) ⟨i.val, by omega⟩ := by
    change glueDirectedVertexMap BL BR (.inl (dartTailVertex BL.map e)) = _
    rw [hev, seam_vertex BL BR]
  by_cases ho : BL.map.IsOuter e
  · have hm := outgoing_outer_mem_left BL e he ho
    have hgm : glueIdentify BL BR (.inl e) ∈ (glueBase BL BR).leftPath.darts := by
      rw [glueBase_leftPath_darts]
      exact List.mem_map.mpr ⟨e, hm, rfl⟩
    exact mem_left_eq_leftmost (glueBase BL BR) _ hgm _ hgv hvs
  · have hsource : v ≠ BL.source := by
      intro h
      have hemem : e ∈ BL.leftPath.darts := by
        have hcsource : c = BL.leftPath.firstDart (by have := BL.left_length_pos; omega) := by
          dsimp only [c]
          simpa only [h] using leftmostOutgoing_source_eq_firstLeftDart BL
        rw [← hce, hcsource]
        exact List.get_mem _ _
      apply ho
      exact (isOuter_iff_mem_outerArcs BL e).mpr
        (Or.inl ((mem_pathCutLeftOuterArc_iff BL e).mpr hemem))
    have hgsource : vertexAt (glueSeamPathBase BL BR) ⟨i.val, by omega⟩ ≠
        (glueBase BL BR).source := by
      rw [seam_vertex BL BR]
      exact fun h => hsource (left_injective BL BR h)
    apply (leftmostOutgoing_internal_characterization (glueBase BL BR) _ hgsource hvs).2.2.2
      _ hgv (left_tail BL BR e he)
    rw [glueBase_map, glueDirectedMap_toCombinatorialMap]
    rw [glue_rot_left_of_inner BL BR e ho, left_tail_iff BL BR]
    have hnot := (leftmostOutgoing_internal_characterization BL v hsource hvt).2.2.1
    simpa only [← hce] using hnot

private theorem prefix_vertex {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {u v : MapVertex M} {n : ℕ}
    (P Q : SimpleDirectedDartPath M u v n) (i : Fin n)
    (hp : P.darts.take i.val = Q.darts.take i.val) :
    vertexAt P ⟨i.val, by omega⟩ = vertexAt Q ⟨i.val, by omega⟩ := by
  by_cases hi : i.val = 0
  · simpa only [vertexAt, hi] using P.start_vertex.trans Q.start_vertex.symm
  · have hip : i.val - 1 < n := by have := i.isLt; omega
    have he := List.getElem_of_eq hp (i := i.val - 1) (by
      simp only [List.length_take, P.darts_length]
      omega)
    have hd : P.darts.get ⟨i.val - 1, by rw [P.darts_length]; exact hip⟩ =
        Q.darts.get ⟨i.val - 1, by rw [Q.darts_length]; exact hip⟩ := by
      simpa only [List.getElem_take, List.get_eq_getElem] using he
    have hidx : i.val - 1 + 1 = i.val := by omega
    have hpv := (P.edge_step ⟨i.val - 1, by rw [P.darts_length]; exact hip⟩).2.2.2
    have hqv := (Q.edge_step ⟨i.val - 1, by rw [Q.darts_length]; exact hip⟩).2.2.2
    simpa only [vertexAt, hidx] using hpv.trans ((congrArg (dartHeadVertex M) hd).trans hqv.symm)






theorem glueSeamPathBase_leftmost (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath)
    (hOrder : ∀ (i : ℕ) (hi : i < s) (e : DL) (d : DR),
      BL.map.tail e →
      dartTailVertex BL.map e = BL.rightPath.vertices.get
        ⟨i, by rw [BL.rightPath.vertices_length]; omega⟩ →
      e ∉ BL.rightPath.darts →
      BR.map.tail d →
      dartTailVertex BR.map d = BR.leftPath.vertices.get
        ⟨i, by rw [BR.leftPath.vertices_length]; omega⟩ →
      d ∉ BR.leftPath.darts →
      ∀ hvs : glueDirectedVertexMap BL BR (.inl (BL.rightPath.vertices.get
          ⟨i, by rw [BL.rightPath.vertices_length]; omega⟩)) ≠ (glueBase BL BR).sink,
      let v := glueDirectedVertexMap BL BR (.inl (BL.rightPath.vertices.get
        ⟨i, by rw [BL.rightPath.vertices_length]; omega⟩))
      let seam := glueIdentify BL BR (.inl (BL.rightPath.darts.get
        ⟨i, by rw [BL.rightPath.darts_length]; exact hi⟩))
      (canonicalOutgoingOrder (glueBase BL BR) v hvs).idxOf (glueIdentify BL BR (.inl e)) <
        (canonicalOutgoingOrder (glueBase BL BR) v hvs).idxOf seam ∧
      (canonicalOutgoingOrder (glueBase BL BR) v hvs).idxOf seam <
        (canonicalOutgoingOrder (glueBase BL BR) v hvs).idxOf (glueIdentify BL BR (.inr d))) :
    IsLexLeftmostXDPGeodesic (glueBase BL BR) x (glueSeamPathBase BL BR) ∧
      IsGeometricLeftmostXDPGeodesic (glueBase BL BR) x (glueSeamPathBase BL BR) := by
  classical
  have hP := glueSeamPathBase_isXDPGeodesic BL BR x hL.1 hR
  have hlex : IsLexLeftmostXDPGeodesic (glueBase BL BR) x (glueSeamPathBase BL BR) := by
    refine ⟨hP, ?_⟩
    intro m Q hQ _ hsm i hpre hdiff
    subst m
    have hv := prefix_vertex (glueSeamPathBase BL BR) Q i hpre
    obtain ⟨d, hd, hdv, hdoff, hdq⟩ := glue_geodesic_seam_departure_right BL BR x hL hR
      Q hQ i hv.symm (Ne.symm hdiff)
    let v := vertexAt (glueSeamPathBase BL BR) ⟨i.val, by omega⟩
    have hvs : v ≠ (glueBase BL BR).sink :=
      simplePath_vertex_ne_end (glueSeamPathBase BL BR) i.val i.isLt
    have htail := (glueSeamPathBase BL BR).edge_step
      ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩
    refine ⟨htail.2.2.1.symm ▸ hvs, ?_⟩
    suffices hs : (canonicalOutgoingOrder (glueBase BL BR) v hvs).idxOf
        ((glueSeamPathBase BL BR).darts.get
          ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩) <
        (canonicalOutgoingOrder (glueBase BL BR) v hvs).idxOf
          (glueIdentify BL BR (.inr d)) by
      rw [hdq] at hs
      have hs' : @List.idxOf (GlueDart BL BR) instBEqOfDecidableEq
          ((glueSeamPathBase BL BR).darts.get
            ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩)
          (canonicalOutgoingOrder (glueBase BL BR) v hvs) <
          @List.idxOf (GlueDart BL BR) instBEqOfDecidableEq
            (Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩)
            (canonicalOutgoingOrder (glueBase BL BR) v hvs) := by
        convert hs using 2 <;> exact lawful_beq_subsingleton _ _
      simpa only [v, vertexAt, ← htail.2.2.1] using hs'
    by_cases hex : ∃ e : DL, BL.map.tail e ∧
        dartTailVertex BL.map e = vertexAt BL.rightPath ⟨i.val, by omega⟩ ∧
        e ∉ BL.rightPath.darts
    · obtain ⟨e, he, hev, heoff⟩ := hex
      have hvs' : glueDirectedVertexMap BL BR (.inl (vertexAt BL.rightPath ⟨i.val, by omega⟩)) ≠
          (glueBase BL BR).sink := by
        rw [← seam_vertex BL BR]
        exact hvs
      have ho := (hOrder i.val i.isLt e d he hev heoff hd hdv hdoff hvs').2
      have hse : (glueSeamPathBase BL BR).darts.get
          ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩ =
          glueIdentify BL BR (.inl (BL.rightPath.darts.get
            ⟨i.val, by rw [BL.rightPath.darts_length]; exact i.isLt⟩)) := List.getElem_map _
      simpa only [v, seam_vertex BL BR, hse] using ho
    · have heq := seam_eq_leftmost_of_no_left BL BR i hex hvs
      obtain ⟨rest, hr⟩ := canonicalOutgoingOrder_cons (glueBase BL BR) v hvs
      rw [← heq] at hr
      rw [hr]
      have hne : glueIdentify BL BR (.inr d) ≠
          (glueSeamPathBase BL BR).darts.get
            ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩ := by
        rw [hdq]
        exact Ne.symm hdiff
      simp only [List.idxOf_cons_self]
      rw [List.idxOf_cons_ne _ hne.symm]
      omega
  exact ⟨hlex, (isLexLeftmost_iff_geometricLeftmost (glueBase BL BR) x
    (glueSeamPathBase BL BR)).mp hlex⟩

end DirectedDistances.PlanarMap
