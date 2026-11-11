module

public import DirectedDistances.PlanarMap.BdyReverseSizedUniform









public section
namespace DirectedDistances.PlanarMap

universe u

variable {D : Type u}

/-- Conjugate a dart permutation by a relabelling permutation. -/
@[expose] def relabelPerm (σ f : Equiv.Perm D) : Equiv.Perm D :=
  σ * f * σ⁻¹

@[simp] theorem relabelPerm_apply (σ f : Equiv.Perm D) (d : D) :
    relabelPerm σ f d = σ (f (σ⁻¹ d)) := by
  simp [relabelPerm, Equiv.Perm.mul_apply]

theorem relabelPerm_one (f : Equiv.Perm D) : relabelPerm 1 f = f := by
  simp [relabelPerm]

theorem relabelPerm_mul (σ τ f : Equiv.Perm D) :
    relabelPerm (σ * τ) f = relabelPerm σ (relabelPerm τ f) := by
  simp only [relabelPerm, mul_inv_rev, mul_assoc]

private theorem sameCycle_relabelPerm (σ f : Equiv.Perm D) {x y : D}
    (h : Equiv.Perm.SameCycle f x y) :
    Equiv.Perm.SameCycle (relabelPerm σ f) (σ x) (σ y) := by
  exact h.conj

private theorem relabelPerm_inv (σ f : Equiv.Perm D) :
    (relabelPerm σ f)⁻¹ = relabelPerm σ f⁻¹ := by
  simp [relabelPerm, mul_assoc]

private theorem relabelPerm_mul_apply (σ f g : Equiv.Perm D) :
    relabelPerm σ (f * g) = relabelPerm σ f * relabelPerm σ g := by
  simp [relabelPerm, mul_assoc]

variable [Fintype D] [DecidableEq D]

/-- Relabel a combinatorial map by conjugating its rotation and edge
involution. -/
@[expose] def CombinatorialMap.relabel (σ : Equiv.Perm D)
    (M : CombinatorialMap D) : CombinatorialMap D where
  edgeInv := relabelPerm σ M.edgeInv
  edgeInv_invol := by
    intro d
    simp [M.edgeInv_invol]
  edgeInv_ne := by
    intro d h
    apply M.edgeInv_ne (σ⁻¹ d)
    apply σ.injective
    calc
      σ (M.edgeInv (σ⁻¹ d)) = d := by simpa only [relabelPerm_apply] using h
      _ = σ (σ⁻¹ d) := by simp
  rot := relabelPerm σ M.rot

@[simp] theorem CombinatorialMap.relabel_edgeInv (σ : Equiv.Perm D)
    (M : CombinatorialMap D) :
    (CombinatorialMap.relabel σ M).edgeInv = relabelPerm σ M.edgeInv := rfl

@[simp] theorem CombinatorialMap.relabel_rot (σ : Equiv.Perm D)
    (M : CombinatorialMap D) :
    (CombinatorialMap.relabel σ M).rot = relabelPerm σ M.rot := rfl

theorem CombinatorialMap.relabel_one (M : CombinatorialMap D) :
    CombinatorialMap.relabel 1 M = M := by
  cases M
  simp [CombinatorialMap.relabel, relabelPerm]

theorem CombinatorialMap.relabel_mul (σ τ : Equiv.Perm D)
    (M : CombinatorialMap D) :
    CombinatorialMap.relabel (σ * τ) M =
      CombinatorialMap.relabel σ (CombinatorialMap.relabel τ M) := by
  cases M
  simp [CombinatorialMap.relabel, relabelPerm, mul_inv_rev, mul_assoc]

theorem CombinatorialMap.relabel_faceSucc (σ : Equiv.Perm D)
    (M : CombinatorialMap D) :
    (CombinatorialMap.relabel σ M).faceSucc = relabelPerm σ M.faceSucc := by
  change (relabelPerm σ M.rot)⁻¹ * relabelPerm σ M.edgeInv =
    relabelPerm σ (M.rot⁻¹ * M.edgeInv)
  rw [relabelPerm_inv, ← relabelPerm_mul_apply]

/-- The face-cycle relation transports dartwise under a relabelling. -/
theorem CombinatorialMap.relabel_isOuter_iff (σ : Equiv.Perm D)
    (M : CombinatorialMap D) (o d : D) :
    CombinatorialMap.IsOuter (CombinatorialMap.relabel σ M) (σ o) (σ d) ↔
      CombinatorialMap.IsOuter M o d := by
  unfold CombinatorialMap.IsOuter
  rw [CombinatorialMap.relabel_faceSucc]
  simp [relabelPerm]

/-- Relabel a directed map with missing edges. Missing and tail predicates
are pulled back along `σ⁻¹`, and its marked outer dart is sent by `σ`. -/
@[expose] def DirectedMapWithMissing.relabel (σ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) : DirectedMapWithMissing D where
  toCombinatorialMap := CombinatorialMap.relabel σ M.toCombinatorialMap
  missing := fun d => M.missing (σ⁻¹ d)
  missing_edgeInv := by
    intro d
    change M.missing (σ⁻¹ d) ↔
      M.missing (σ⁻¹ (σ (M.toCombinatorialMap.edgeInv (σ⁻¹ d))))
    simpa using M.missing_edgeInv (σ⁻¹ d)
  tail := fun d => M.tail (σ⁻¹ d)
  tail_iff := by
    intro d hd
    have hd' : ¬ M.missing (σ⁻¹ d) := hd
    change M.tail (σ⁻¹ d) ↔
      ¬ M.tail (σ⁻¹ (σ (M.toCombinatorialMap.edgeInv (σ⁻¹ d))))
    simpa using M.tail_iff (σ⁻¹ d) hd'
  tail_missing := by
    intro d hd
    exact M.tail_missing (σ⁻¹ d) hd
  outer := σ M.outer
  missing_outer := by
    intro d hd
    have houter := M.missing_outer (σ⁻¹ d) hd
    rcases houter with houter | houter
    · left
      simpa using (CombinatorialMap.relabel_isOuter_iff σ
        M.toCombinatorialMap M.outer (σ⁻¹ d)).2 houter
    · right
      have houter' := (CombinatorialMap.relabel_isOuter_iff σ
        M.toCombinatorialMap M.outer (M.toCombinatorialMap.edgeInv (σ⁻¹ d))).2 houter
      simpa using houter'

@[simp] theorem DirectedMapWithMissing.relabel_combinatorialMap
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) :
    (DirectedMapWithMissing.relabel σ M).toCombinatorialMap =
      CombinatorialMap.relabel σ M.toCombinatorialMap := rfl

@[simp] theorem DirectedMapWithMissing.relabel_missing
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) (d : D) :
    (DirectedMapWithMissing.relabel σ M).missing d ↔ M.missing (σ⁻¹ d) := Iff.rfl

@[simp] theorem DirectedMapWithMissing.relabel_tail
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) (d : D) :
    (DirectedMapWithMissing.relabel σ M).tail d ↔ M.tail (σ⁻¹ d) := Iff.rfl

@[simp] theorem DirectedMapWithMissing.relabel_outer
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) :
    (DirectedMapWithMissing.relabel σ M).outer = σ M.outer := rfl

theorem DirectedMapWithMissing.relabel_one (M : DirectedMapWithMissing D) :
    DirectedMapWithMissing.relabel 1 M = M := by
  cases M
  simp [DirectedMapWithMissing.relabel, CombinatorialMap.relabel,
    relabelPerm]

theorem DirectedMapWithMissing.relabel_mul (σ τ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) :
    DirectedMapWithMissing.relabel (σ * τ) M =
      DirectedMapWithMissing.relabel σ (DirectedMapWithMissing.relabel τ M) := by
  cases M
  simp [DirectedMapWithMissing.relabel, CombinatorialMap.relabel,
    relabelPerm, mul_inv_rev, mul_assoc]

instance instMulActionCombinatorialMap : MulAction (Equiv.Perm D)
    (CombinatorialMap D) where
  smul := fun σ M => CombinatorialMap.relabel σ M
  one_smul := CombinatorialMap.relabel_one
  mul_smul := CombinatorialMap.relabel_mul

instance instMulActionDirectedMapWithMissing : MulAction (Equiv.Perm D)
    (DirectedMapWithMissing D) where
  smul := fun σ M => DirectedMapWithMissing.relabel σ M
  one_smul := DirectedMapWithMissing.relabel_one
  mul_smul := DirectedMapWithMissing.relabel_mul

/-- The image of a dart set under a relabelling permutation. -/
@[expose] def relabelDartSet (σ : Equiv.Perm D) (S : Set D) : Set D := σ '' S

/-- The edge-orbit-closed dart set selected by a prefix of a path. This is the
underlying set in `rightPrefixFlipDarts` -/
@[expose] def prefixFlipDartSet (M : CombinatorialMap D)
    (pathDarts : List D) (k : ℕ) : Set D :=
  {d | d ∈ pathDarts.take k ∨ M.edgeInv d ∈ pathDarts.take k}

omit [Fintype D] [DecidableEq D] in
theorem relabelDartSet_mem (σ : Equiv.Perm D) (S : Set D) (d : D) :
    d ∈ relabelDartSet σ S ↔ σ.symm d ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨σ.symm d, h, by simp⟩

@[simp] theorem DirectedMapWithMissing.relabel_missing_set
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) :
    {d | (DirectedMapWithMissing.relabel σ M).missing d} =
      relabelDartSet σ {d | M.missing d} := by
  ext d
  simp [Set.mem_ofPred_eq, DirectedMapWithMissing.relabel_missing,
    relabelDartSet_mem]

@[simp] theorem DirectedMapWithMissing.relabel_tail_set
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) :
    {d | (DirectedMapWithMissing.relabel σ M).tail d} =
      relabelDartSet σ {d | M.tail d} := by
  ext d
  simp [Set.mem_ofPred_eq, DirectedMapWithMissing.relabel_tail,
    relabelDartSet_mem]

/-- The right-prefix flip set is exactly the generic prefix set of its right
boundary path. -/
theorem rightPrefixFlipDarts_eq_prefixFlipDartSet
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ) :
    rightPrefixFlipDarts B k =
      prefixFlipDartSet B.map.toCombinatorialMap B.rightPath.darts k := rfl

/-- The edge-orbit-closed selected prefix set transports by the relabelling.
This is the set-level reversal datum before boundary proof fields are rebuilt. -/
theorem relabel_prefixFlipDartSet (σ : Equiv.Perm D) (M : CombinatorialMap D)
    (pathDarts : List D) (k : ℕ) :
    relabelDartSet σ (prefixFlipDartSet M pathDarts k) =
      prefixFlipDartSet (CombinatorialMap.relabel σ M) (pathDarts.map σ) k := by
  ext d
  rw [relabelDartSet_mem]
  change (σ.symm d ∈ pathDarts.take k ∨
      M.edgeInv (σ.symm d) ∈ pathDarts.take k) ↔
    (d ∈ (pathDarts.map σ).take k ∨
      (CombinatorialMap.relabel σ M).edgeInv d ∈ (pathDarts.map σ).take k)
  have hprefix (x : D) :
      σ x ∈ (pathDarts.take k).map σ ↔ x ∈ pathDarts.take k := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := σ.injective hxy
      simpa [hyx] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hfirst : d ∈ (pathDarts.map σ).take k ↔
      σ.symm d ∈ pathDarts.take k := by
    rw [← List.map_take]
    simpa using hprefix (σ.symm d)
  have hsecond : (CombinatorialMap.relabel σ M).edgeInv d ∈
      (pathDarts.map σ).take k ↔ M.edgeInv (σ.symm d) ∈ pathDarts.take k := by
    rw [← List.map_take]
    have heq : (CombinatorialMap.relabel σ M).edgeInv d =
        σ (M.edgeInv (σ.symm d)) := by
      simp [CombinatorialMap.relabel_edgeInv, relabelPerm_apply]
    rw [heq]
    exact hprefix _
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (hfirst.mpr h)
    · exact Or.inr (hsecond.mpr h)
  · intro h
    rcases h with h | h
    · exact Or.inl (hfirst.mp h)
    · exact Or.inr (hsecond.mp h)

theorem DirectedMapWithMissing.relabel_isOuter_set
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) :
    {d | (DirectedMapWithMissing.relabel σ M).IsOuter d} =
      relabelDartSet σ {d | M.IsOuter d} := by
  ext d
  rw [relabelDartSet_mem]
  constructor
  · intro h
    have h' : CombinatorialMap.IsOuter
        (CombinatorialMap.relabel σ M.toCombinatorialMap)
        (σ M.outer) (σ (σ.symm d)) := by
      simpa [DirectedMapWithMissing.IsOuter] using h
    exact (CombinatorialMap.relabel_isOuter_iff σ M.toCombinatorialMap
      M.outer (σ.symm d)).1 h'
  · intro h
    have h' : CombinatorialMap.IsOuter M.toCombinatorialMap M.outer
        (σ.symm d) := by simpa [DirectedMapWithMissing.IsOuter] using h
    have h'' := (CombinatorialMap.relabel_isOuter_iff σ M.toCombinatorialMap
      M.outer (σ.symm d)).2 h'
    simpa [DirectedMapWithMissing.IsOuter] using h''

/-- The dart relabelling induces an equivalence of rotation-cycle vertices. -/
@[expose] noncomputable def DirectedMapWithMissing.relabelVertexEquiv
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) :
    MapVertex M ≃ MapVertex (DirectedMapWithMissing.relabel σ M) := by
  classical
  apply Quotient.congr σ
  intro x y
  change Equiv.Perm.SameCycle M.toCombinatorialMap.rot x y ↔
    Equiv.Perm.SameCycle (relabelPerm σ M.toCombinatorialMap.rot) (σ x) (σ y)
  constructor
  · intro h
    exact h.conj
  · intro h
    simpa [relabelPerm] using
      (Equiv.Perm.sameCycle_conj (g := σ)
        (f := M.toCombinatorialMap.rot) (x := σ x) (y := σ y)).mp h

@[simp] theorem DirectedMapWithMissing.relabelVertexEquiv_dartTailVertex
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) (d : D) :
    DirectedMapWithMissing.relabelVertexEquiv σ M (dartTailVertex M d) =
      dartTailVertex (DirectedMapWithMissing.relabel σ M) (σ d) := by
  change Quotient.congr σ _ (Quotient.mk _ d) = Quotient.mk _ (σ d)
  exact Quotient.congr_mk σ _ d

@[simp] theorem DirectedMapWithMissing.relabelVertexEquiv_dartHeadVertex
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) (d : D) :
    DirectedMapWithMissing.relabelVertexEquiv σ M (dartHeadVertex M d) =
      dartHeadVertex (DirectedMapWithMissing.relabel σ M) (σ d) := by
  change DirectedMapWithMissing.relabelVertexEquiv σ M
      (dartTailVertex M (M.toCombinatorialMap.edgeInv d)) =
    dartTailVertex (DirectedMapWithMissing.relabel σ M)
      ((DirectedMapWithMissing.relabel σ M).toCombinatorialMap.edgeInv (σ d))
  rw [DirectedMapWithMissing.relabelVertexEquiv_dartTailVertex]
  simp [CombinatorialMap.relabel_edgeInv, relabelPerm_apply]

/-- Transport a simple directed dart path along the relabelling of its map.
Both its dart list and its quotient-valued vertex list are mapped. -/
@[expose] noncomputable def SimpleDirectedDartPath.relabel
    (σ : Equiv.Perm D) {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    SimpleDirectedDartPath (DirectedMapWithMissing.relabel σ M)
      (DirectedMapWithMissing.relabelVertexEquiv σ M s)
      (DirectedMapWithMissing.relabelVertexEquiv σ M t) n where
  darts := P.darts.map σ
  vertices := P.vertices.map (DirectedMapWithMissing.relabelVertexEquiv σ M)
  darts_length := by simp [P.darts_length]
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map
    (DirectedMapWithMissing.relabelVertexEquiv σ M).injective
  start_vertex := by
    simpa using congrArg (DirectedMapWithMissing.relabelVertexEquiv σ M)
      P.start_vertex
  end_vertex := by
    simpa using congrArg (DirectedMapWithMissing.relabelVertexEquiv σ M)
      P.end_vertex
  edge_step := by
    intro i
    have hi : i.val < n := by simpa [P.darts_length] using i.isLt
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
    let jv : Fin P.vertices.length := ⟨i.val, by
      rw [P.vertices_length]
      omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by
      rw [P.vertices_length]
      omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map σ).get i = σ (P.darts.get j) := by
      simp [j]
    have hgetV : (P.vertices.map (DirectedMapWithMissing.relabelVertexEquiv σ M)).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          DirectedMapWithMissing.relabelVertexEquiv σ M (P.vertices.get jv) := by
      simp [jv]
    have hgetV' : (P.vertices.map (DirectedMapWithMissing.relabelVertexEquiv σ M)).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          DirectedMapWithMissing.relabelVertexEquiv σ M (P.vertices.get jv') := by
      simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h.1
    · simpa using h.2.1
    · calc
        (P.vertices.map (DirectedMapWithMissing.relabelVertexEquiv σ M)).get
            ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            DirectedMapWithMissing.relabelVertexEquiv σ M (P.vertices.get jv) := hgetV
        _ = DirectedMapWithMissing.relabelVertexEquiv σ M
            (dartTailVertex M (P.darts.get j)) := congrArg _ h.2.2.1
        _ = dartTailVertex (DirectedMapWithMissing.relabel σ M)
            (σ (P.darts.get j)) :=
          DirectedMapWithMissing.relabelVertexEquiv_dartTailVertex σ M _
    · calc
        (P.vertices.map (DirectedMapWithMissing.relabelVertexEquiv σ M)).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            DirectedMapWithMissing.relabelVertexEquiv σ M (P.vertices.get jv') := hgetV'
        _ = DirectedMapWithMissing.relabelVertexEquiv σ M
            (dartHeadVertex M (P.darts.get j)) := congrArg _ h.2.2.2
        _ = dartHeadVertex (DirectedMapWithMissing.relabel σ M)
            (σ (P.darts.get j)) :=
          DirectedMapWithMissing.relabelVertexEquiv_dartHeadVertex σ M _

@[simp] theorem SimpleDirectedDartPath.relabel_darts
    (σ : Equiv.Perm D) {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    (SimpleDirectedDartPath.relabel σ P).darts = P.darts.map σ := rfl

@[simp] theorem SimpleDirectedDartPath.relabel_vertices
    (σ : Equiv.Perm D) {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    (SimpleDirectedDartPath.relabel σ P).vertices =
      P.vertices.map (DirectedMapWithMissing.relabelVertexEquiv σ M) := rfl

/-- Relabel every letter in a nonempty cyclic-word representative. -/
@[expose] def NonemptyWord.relabel (σ : Equiv.Perm D) (W : NonemptyWord D) :
    NonemptyWord D where
  letters := W.letters.map σ
  nonempty := by
    intro h
    apply W.nonempty
    exact List.map_eq_nil_iff.mp h
  nodup := W.nodup.map σ.injective

omit [Fintype D] [DecidableEq D] in
@[simp] theorem NonemptyWord.relabel_letters (σ : Equiv.Perm D)
    (W : NonemptyWord D) : (NonemptyWord.relabel σ W).letters = W.letters.map σ := rfl

/-- The dart list for a reversed right prefix is equivariant under relabelling.
This is the list formula in `rightPrefixReversal_leftPath_darts`
not yet provided here. -/
theorem relabel_rightPrefixLeftDarts (σ : Equiv.Perm D)
    (M : CombinatorialMap D) (left right : List D) (k : ℕ) :
    ((right.map σ).take k).reverse.map
      (CombinatorialMap.relabel σ M).edgeInv ++ left.map σ =
      ((right.take k).reverse.map M.edgeInv ++ left).map σ := by
  have hfun : (fun d => relabelPerm σ M.edgeInv (σ d)) =
      fun d => σ (M.edgeInv d) := by
    funext d
    simp [relabelPerm]
  simp only [List.map_take, List.map_reverse, List.map_append, List.map_map,
    CombinatorialMap.relabel_edgeInv, Function.comp_def]
  rw [hfun]

omit [Fintype D] [DecidableEq D] in
/-- The dart list for the retained right suffix is equivariant under
relabelling. This is the list formula in `rightPrefixReversal_rightPath_darts` -/
theorem relabel_rightPrefixRightDarts (σ : Equiv.Perm D)
    (right : List D) (k : ℕ) :
    (right.map σ).drop k = (right.drop k).map σ := by
  simp

/-- The dart list for a reversed left prefix is equivariant under relabelling.
This is the list formula in `leftPrefixReversal_rightPath_darts` -/
theorem relabel_leftPrefixRightDarts (σ : Equiv.Perm D)
    (M : CombinatorialMap D) (left right : List D) (k : ℕ) :
    ((left.map σ).take k).reverse.map
      (CombinatorialMap.relabel σ M).edgeInv ++ right.map σ =
      ((left.take k).reverse.map M.edgeInv ++ right).map σ := by
  exact relabel_rightPrefixLeftDarts σ M right left k

end DirectedDistances.PlanarMap
