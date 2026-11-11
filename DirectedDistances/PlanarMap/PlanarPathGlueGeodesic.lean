module

public import DirectedDistances.PlanarMap.PlanarPathGlueBase
public import DirectedDistances.PlanarMap.PlanarPathCutNoStrictLeft

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PlanarMap

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)

private theorem directed_vertex_eq (v w : MapVertex BL.map ⊕ MapVertex BR.map) :
    glueDirectedVertexMap BL BR v = glueDirectedVertexMap BL BR w ↔
      glueVertexMap BL BR v = glueVertexMap BL BR w := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      refine Quotient.inductionOn₂ v w ?_
      intro d e
      change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
      rw [Quotient.eq, Quotient.eq]
      change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
      rw [glueDirectedMap_toCombinatorialMap]
      rfl
    | inr w =>
      refine Quotient.inductionOn₂ v w ?_
      intro d e
      change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
      rw [Quotient.eq, Quotient.eq]
      change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
      rw [glueDirectedMap_toCombinatorialMap]
      rfl
  | inr v =>
    cases w with
    | inl w =>
      refine Quotient.inductionOn₂ v w ?_
      intro d e
      change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
      rw [Quotient.eq, Quotient.eq]
      change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
      rw [glueDirectedMap_toCombinatorialMap]
      rfl
    | inr w =>
      refine Quotient.inductionOn₂ v w ?_
      intro d e
      change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
      rw [Quotient.eq, Quotient.eq]
      change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
      rw [glueDirectedMap_toCombinatorialMap]
      rfl

private theorem left_tail (d : DL) (ht : BL.map.tail d) :
    (glueDirectedMap BL BR).tail (glueIdentify BL BR (.inl d)) := by
  have hd : BL.map.toCombinatorialMap.edgeInv d ∉ BL.rightPath.darts := by
    intro hm
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    exact (BL.map.tail_iff d (BL.noMissingDarts d)).mp ht
      (hj ▸ (BL.rightPath.edge_step j).2.1)
  rw [glueIdentify_inl_kept BL BR ⟨d, hd⟩, glueDirectedMap_tail]
  exact ht

private theorem left_head (d : DL) :
    dartHeadVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inl d)) =
      glueDirectedVertexMap BL BR (.inl (dartHeadVertex BL.map d)) := by
  change dartTailVertex (glueDirectedMap BL BR)
    ((glueDirectedMap BL BR).toCombinatorialMap.edgeInv (glueIdentify BL BR (.inl d))) = _
  rw [glueDirectedMap_toCombinatorialMap, glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl



@[expose] noncomputable def glueSeamPath :
    SimpleDirectedDartPath (glueDirectedMap BL BR)
      (glueDirectedVertexMap BL BR (.inl BL.source))
      (glueDirectedVertexMap BL BR (.inl BL.sink)) s :=
  glueMapSimpleDirectedDartPath (fun v => glueDirectedVertexMap BL BR (.inl v))
    (fun d => glueIdentify BL BR (.inl d))
    (by intro _ _ h; exact glueVertexMap_left_injective BL BR ((directed_vertex_eq BL BR _ _).mp h))
    (fun _ => glueDirectedMap_noMissing BL BR _) (by exact left_tail BL BR)
    (fun _ => rfl) (by exact left_head BL BR) rfl rfl BL.rightPath



theorem glueSeamPath_darts :
    (glueSeamPath BL BR).darts =
      BL.rightPath.darts.map (fun d => glueIdentify BL BR (.inl d)) := rfl




theorem geodesic_sideSegment_ldp
    {D : Type*} [Fintype D] [DecidableEq D] {a b n k : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D a b)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsXDPGeodesicBase B .ldp P) (i j : Fin (n + 1))
    (Q : SimpleDirectedDartPath B.map
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩)
      (P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩) k) :
    k ≤ j.val - i.val ∧ i.val ≤ j.val := by
  have h := hP (((P.prefix i).appendAcyclic B.map B.acyclic Q).appendAcyclic
    B.map B.acyclic (P.suffix j))
  have hj := j.isLt
  omega




theorem geodesic_sideSegment_sdp
    {D : Type*} [Fintype D] [DecidableEq D] {a b n k : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D a b)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsXDPGeodesicBase B .sdp P) (i j : Fin (n + 1))
    (Q : SimpleDirectedDartPath B.map
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩)
      (P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩) k) :
    j.val - i.val ≤ k := by
  have h := hP (((P.prefix i).appendAcyclic B.map B.acyclic Q).appendAcyclic
    B.map B.acyclic (P.suffix j))
  have hj := j.isLt
  omega

private theorem directed_surjective : Function.Surjective (glueDirectedVertexMap BL BR) := by
  intro v
  refine Quotient.inductionOn v ?_
  intro a
  obtain ⟨d | d, rfl⟩ := glueIdentify_surjective BL BR a
  · exact ⟨.inl (dartTailVertex BL.map d), rfl⟩
  · exact ⟨.inr (dartTailVertex BR.map d), rfl⟩

private noncomputable def gluedPotential
    (fL : MapVertex BL.map → ℕ) (fR : MapVertex BR.map → ℕ)
    (v : MapVertex (glueDirectedMap BL BR)) : ℕ :=
  Sum.elim fL fR (Classical.choose (directed_surjective BL BR v))

private theorem potential_compatible
    (fL : MapVertex BL.map → ℕ) (fR : MapVertex BR.map → ℕ)
    (h : ∀ i : Fin (s + 1),
      fL (dartTailVertex BL.map (glueLeftSeamVertexDart BL i)) =
      fR (dartTailVertex BR.map (glueRightSeamVertexDart BR i)))
    (v w : MapVertex BL.map ⊕ MapVertex BR.map)
    (he : glueDirectedVertexMap BL BR v = glueDirectedVertexMap BL BR w) :
    Sum.elim fL fR v = Sum.elim fL fR w := by
  have he' := (directed_vertex_eq BL BR v w).mp he
  cases v with
  | inl v =>
    cases w with
    | inl w => exact congrArg fL (glueVertexMap_left_injective BL BR he')
    | inr w =>
      obtain ⟨i, rfl, rfl⟩ := (glueVertexMap_cross_iff BL BR v w).mp he'
      exact h i
  | inr v =>
    cases w with
    | inl w =>
      obtain ⟨i, rfl, rfl⟩ := (glueVertexMap_cross_iff BL BR w v).mp he'.symm
      exact (h i).symm
    | inr w => exact congrArg fR (glueVertexMap_right_injective BL BR he')

private theorem gluedPotential_apply
    (fL : MapVertex BL.map → ℕ) (fR : MapVertex BR.map → ℕ)
    (h : ∀ i : Fin (s + 1),
      fL (dartTailVertex BL.map (glueLeftSeamVertexDart BL i)) =
      fR (dartTailVertex BR.map (glueRightSeamVertexDart BR i)))
    (v : MapVertex BL.map ⊕ MapVertex BR.map) :
    gluedPotential BL BR fL fR (glueDirectedVertexMap BL BR v) = Sum.elim fL fR v := by
  exact potential_compatible BL BR fL fR h _ v
    (Classical.choose_spec (directed_surjective BL BR (glueDirectedVertexMap BL BR v)))

private theorem geodesic_source_index
    {D : Type*} [Fintype D] [DecidableEq D] {a b n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D a b) (x : XDP)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsXDPGeodesicBase B x P) (i : Fin (n + 1)) :
    xdpSourceDistanceNatBase B x
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩) = i.val := by
  cases x with
  | ldp => exact (IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP i).1
  | sdp => exact (IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP i).1

private theorem source_potential_compatible (x : XDP)
    (hL : IsXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) (i : Fin (s + 1)) :
    xdpSourceDistanceNatBase BL x (dartTailVertex BL.map (glueLeftSeamVertexDart BL i)) =
      xdpSourceDistanceNatBase BR x (dartTailVertex BR.map (glueRightSeamVertexDart BR i)) := by
  rw [glueLeftSeamVertexDart_vertex, glueRightSeamVertexDart_vertex,
    geodesic_source_index BL x BL.rightPath hL i,
    geodesic_source_index BR x BR.leftPath hR i]

private theorem source_potential_step
    {D : Type*} [Fintype D] [DecidableEq D] {a b : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D a b) (x : XDP)
    {u v : MapVertex B.map} (h : B.map.directedStep u v) :
    match (generalizing := false) x with
    | .ldp => xdpSourceDistanceNatBase B x u + 1 ≤ xdpSourceDistanceNatBase B x v
    | .sdp => xdpSourceDistanceNatBase B x v ≤ xdpSourceDistanceNatBase B x u + 1 := by
  obtain ⟨d, _, ht, rfl, rfl⟩ := h
  cases x with
  | ldp => exact ldpSourceDistanceNatBase_step B d ht
  | sdp => exact sdpSourceDistanceNatBase_step B d ht

private theorem glued_potential_step (x : XDP)
    (hL : IsXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath)
    {u v : MapVertex (glueDirectedMap BL BR)}
    (h : (glueDirectedMap BL BR).directedStep u v) :
    let f := gluedPotential BL BR (xdpSourceDistanceNatBase BL x) (xdpSourceDistanceNatBase BR x)
    match (generalizing := false) x with
    | .ldp => f u + 1 ≤ f v
    | .sdp => f v ≤ f u + 1 := by
  have hc := source_potential_compatible BL BR x hL hR
  rcases (glue_directedStep_iff BL BR u v).mp h with
    ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
  · dsimp only
    rw [gluedPotential_apply BL BR _ _ hc (.inl a),
      gluedPotential_apply BL BR _ _ hc (.inl b)]
    have hs := source_potential_step BL x hab
    cases x <;> exact hs
  · dsimp only
    rw [gluedPotential_apply BL BR _ _ hc (.inr a),
      gluedPotential_apply BL BR _ _ hc (.inr b)]
    have hs := source_potential_step BR x hab
    cases x <;> exact hs

private theorem path_potential_bound
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (f : MapVertex M → ℕ) (x : XDP)
    (hf : ∀ u v, M.directedStep u v → match (generalizing := false) x with
      | .ldp => f u + 1 ≤ f v
      | .sdp => f v ≤ f u + 1) :
    match (generalizing := false) x with
    | .ldp => f a + n ≤ f b
    | .sdp => f b ≤ f a + n := by
  have hd := P.darts_length
  have hv := P.vertices_length
  have hi : ∀ j : ℕ, (hj : j ≤ n) → match (generalizing := false) x with
      | .ldp => f a + j ≤ f (P.vertices.get ⟨j, by omega⟩)
      | .sdp => f (P.vertices.get ⟨j, by omega⟩) ≤ f a + j := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hstart := P.start_vertex
      cases x <;> simpa only [hstart, Nat.add_zero] using Nat.le_refl (f a)
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hs := P.edge_step ⟨j, by omega⟩
      have he : M.directedStep
          (P.vertices.get ⟨j, by omega⟩) (P.vertices.get ⟨j + 1, by omega⟩) :=
        ⟨_, hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩
      have hstep := hf _ _ he
      cases x <;> dsimp only at hprev hstep ⊢ <;> omega
  have h := hi n (by omega)
  simpa only [P.end_vertex] using h





theorem glue_path_length_bound (x : XDP)
    (hL : IsXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) {k : ℕ}
    (Q : SimpleDirectedDartPath (glueDirectedMap BL BR)
      (glueDirectedVertexMap BL BR (.inl BL.source))
      (glueDirectedVertexMap BL BR (.inl BL.sink)) k) :
    match (generalizing := false) x with
    | .ldp => k ≤ s
    | .sdp => s ≤ k := by
  let f := gluedPotential BL BR (xdpSourceDistanceNatBase BL x) (xdpSourceDistanceNatBase BR x)
  have hc := source_potential_compatible BL BR x hL hR
  have hf0 : f (glueDirectedVertexMap BL BR (.inl BL.source)) = 0 := by
    dsimp only [f]
    rw [gluedPotential_apply BL BR _ _ hc (.inl BL.source)]
    have h := geodesic_source_index BL x BL.rightPath hL ⟨0, by omega⟩
    simpa only [BL.rightPath.start_vertex, Sum.elim_inl] using h
  have hfs : f (glueDirectedVertexMap BL BR (.inl BL.sink)) = s := by
    dsimp only [f]
    rw [gluedPotential_apply BL BR _ _ hc (.inl BL.sink)]
    have h := geodesic_source_index BL x BL.rightPath hL ⟨s, by omega⟩
    simpa only [BL.rightPath.end_vertex, Sum.elim_inl] using h
  have hf : ∀ u v, (glueDirectedMap BL BR).directedStep u v → match (generalizing := false) x with
      | .ldp => f u + 1 ≤ f v
      | .sdp => f v ≤ f u + 1 := by
    intro u v h
    have hs := glued_potential_step BL BR x hL hR h
    cases x <;> exact hs
  have h := path_potential_bound Q f x hf
  cases x <;> dsimp only at h ⊢ <;> simpa only [hf0, hfs, Nat.zero_add] using h



theorem glue_left_sideSegment_bound (x : XDP)
    (hL : IsXDPGeodesicBase BL x BL.rightPath) (i j : Fin (s + 1)) {k : ℕ}
    (Q : SimpleDirectedDartPath BL.map
      (dartTailVertex BL.map (glueLeftSeamVertexDart BL i))
      (dartTailVertex BL.map (glueLeftSeamVertexDart BL j)) k) :
    match (generalizing := false) x with
    | .ldp => k ≤ j.val - i.val ∧ i.val ≤ j.val
    | .sdp => j.val - i.val ≤ k := by
  rw [glueLeftSeamVertexDart_vertex, glueLeftSeamVertexDart_vertex] at Q
  cases x with
  | ldp => exact geodesic_sideSegment_ldp BL BL.rightPath hL i j Q
  | sdp => exact geodesic_sideSegment_sdp BL BL.rightPath hL i j Q



theorem glue_right_sideSegment_bound (x : XDP)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) (i j : Fin (s + 1)) {k : ℕ}
    (Q : SimpleDirectedDartPath BR.map
      (dartTailVertex BR.map (glueRightSeamVertexDart BR i))
      (dartTailVertex BR.map (glueRightSeamVertexDart BR j)) k) :
    match (generalizing := false) x with
    | .ldp => k ≤ j.val - i.val ∧ i.val ≤ j.val
    | .sdp => j.val - i.val ≤ k := by
  rw [glueRightSeamVertexDart_vertex, glueRightSeamVertexDart_vertex] at Q
  cases x with
  | ldp => exact geodesic_sideSegment_ldp BR BR.leftPath hR i j Q
  | sdp => exact geodesic_sideSegment_sdp BR BR.leftPath hR i j Q




theorem glueSeamPath_extremal_length (x : XDP)
    (hL : IsXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) :
    match (generalizing := false) x with
    | .ldp => IsGreatest {k : ℕ | Nonempty (SimpleDirectedDartPath (glueDirectedMap BL BR)
        (glueDirectedVertexMap BL BR (.inl BL.source))
        (glueDirectedVertexMap BL BR (.inl BL.sink)) k)} s
    | .sdp => IsLeast {k : ℕ | Nonempty (SimpleDirectedDartPath (glueDirectedMap BL BR)
        (glueDirectedVertexMap BL BR (.inl BL.source))
        (glueDirectedVertexMap BL BR (.inl BL.sink)) k)} s := by
  cases x with
  | ldp =>
    refine ⟨⟨glueSeamPath BL BR⟩, ?_⟩
    rintro k ⟨Q⟩
    exact glue_path_length_bound BL BR .ldp hL hR Q
  | sdp =>
    refine ⟨⟨glueSeamPath BL BR⟩, ?_⟩
    rintro k ⟨Q⟩
    exact glue_path_length_bound BL BR .sdp hL hR Q

end DirectedDistances.PlanarMap
