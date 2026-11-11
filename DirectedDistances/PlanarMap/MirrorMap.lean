/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarBoundaryData

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombinatorialMap

/-- Reverse the rotation order while retaining the edge darts and edge
involution. This is the combinatorial reflection of the map -/
@[expose] def mirror (M : CombinatorialMap D) : CombinatorialMap D where
  edgeInv := M.edgeInv
  edgeInv_invol := M.edgeInv_invol
  edgeInv_ne := M.edgeInv_ne
  rot := M.rot⁻¹

private theorem edgeInv_inv (M : CombinatorialMap D) : M.edgeInv⁻¹ = M.edgeInv := by
  ext d
  apply M.edgeInv.injective
  simp [M.edgeInv_invol]

private theorem edgeInv_mul_self (M : CombinatorialMap D) : M.edgeInv * M.edgeInv = 1 := by
  ext d
  exact M.edgeInv_invol d

/-- Reflecting twice recovers the original combinatorial map. -/
theorem mirror_mirror (M : CombinatorialMap D) : M.mirror.mirror = M := by
  cases M
  rfl

/-- The mirror face permutation is the edge-involution conjugate of the
inverse original face permutation. -/
theorem mirror_faceSucc (M : CombinatorialMap D) :
    M.mirror.faceSucc = M.edgeInv * M.faceSucc⁻¹ * M.edgeInv := by
  calc
    M.mirror.faceSucc = M.rot * M.edgeInv := by simp [faceSucc, mirror]
    _ = M.edgeInv * M.faceSucc⁻¹ * M.edgeInv := by
      rw [faceSucc, mul_inv_rev, edgeInv_inv, inv_inv]
      rw [← mul_assoc, edgeInv_mul_self, one_mul]

private theorem faceMirrorSameCycle (M : CombinatorialMap D) (a b : D) :
    M.mirror.faceSucc.SameCycle (M.edgeInv a) (M.edgeInv b) ↔
      M.faceSucc.SameCycle a b := by
  simpa [mirror_faceSucc, edgeInv_inv, M.edgeInv_invol] using
    (Equiv.Perm.sameCycle_conj (f := M.faceSucc⁻¹) (g := M.edgeInv)
      (x := M.edgeInv a) (y := M.edgeInv b))

/-- Rotation-cycle vertices are unchanged by mirroring. -/
def vertexQuotientEquiv (M : CombinatorialMap D) :
    VertexQuotient M ≃ VertexQuotient M.mirror where
  toFun := Quotient.map id (by
    intro a b hab
    exact Equiv.Perm.sameCycle_inv.mpr hab)
  invFun := Quotient.map id (by
    intro a b hab
    exact Equiv.Perm.sameCycle_inv.mp hab)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h d => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h d => rfl

 
def edgeQuotientEquiv (M : CombinatorialMap D) :
    EdgeQuotient M ≃ EdgeQuotient M.mirror := Equiv.refl _

/-- Face-cycle quotients are identified by sending each dart to its opposite
dart. -/
def faceQuotientEquiv (M : CombinatorialMap D) :
    FaceQuotient M ≃ FaceQuotient M.mirror where
  toFun := Quotient.map M.edgeInv (by
    intro a b hab
    exact (faceMirrorSameCycle M a b).2 hab)
  invFun := Quotient.map M.edgeInv (by
    intro a b hab
    change M.mirror.faceSucc.SameCycle a b at hab
    have hab' : M.mirror.faceSucc.SameCycle
        (M.edgeInv (M.edgeInv a)) (M.edgeInv (M.edgeInv b)) := by
      rw [M.edgeInv_invol, M.edgeInv_invol]
      exact hab
    exact (faceMirrorSameCycle M (M.edgeInv a) (M.edgeInv b)).mp hab')
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h d => simp [M.edgeInv_invol]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h d => simp [M.edgeInv_invol]

/-- Mirroring preserves the number of vertices. -/
theorem numVertices_mirror (M : CombinatorialMap D) :
    M.mirror.numVertices = M.numVertices := by
  classical
  exact Fintype.card_congr (vertexQuotientEquiv M).symm

/-- Mirroring preserves the number of edges. -/
theorem numEdges_mirror (M : CombinatorialMap D) :
    M.mirror.numEdges = M.numEdges := by
  classical
  exact Fintype.card_congr (edgeQuotientEquiv M).symm

/-- Mirroring preserves the number of faces. -/
theorem numFaces_mirror (M : CombinatorialMap D) :
    M.mirror.numFaces = M.numFaces := by
  classical
  exact Fintype.card_congr (faceQuotientEquiv M).symm

private theorem reflTransGen_mono_iff {α : Type*} {r s : α → α → Prop}
    (hrs : ∀ x y, r x y ↔ s x y) {a b : α} :
    Relation.ReflTransGen r a b ↔ Relation.ReflTransGen s a b := by
  constructor <;> intro h
  · induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hstep ih =>
        exact Relation.ReflTransGen.tail ih ((hrs _ _).mp hstep)
  · induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hstep ih =>
        exact Relation.ReflTransGen.tail ih ((hrs _ _).mpr hstep)

/-- Combinatorial connectedness is invariant under reversing rotation order. -/
theorem isConnected_mirror_iff (M : CombinatorialMap D) :
    M.mirror.IsConnected ↔ M.IsConnected := by
  constructor <;> intro h d e
  · exact (reflTransGen_mono_iff (fun x y => by
      simp only [mirror]
      tauto) (a := d) (b := e)).mp (h d e)
  · exact (reflTransGen_mono_iff (fun x y => by
      simp only [mirror]
      tauto) (a := d) (b := e)).mpr (h d e)

/-- Combinatorial planarity is invariant under mirroring. -/
theorem isPlanar_mirror_iff (M : CombinatorialMap D) :
    M.mirror.IsPlanar ↔ M.IsPlanar := by
  rw [IsPlanar, IsPlanar, isConnected_mirror_iff]
  simp [eulerChar, numVertices_mirror, numEdges_mirror, numFaces_mirror]

end CombinatorialMap

namespace DirectedMapWithMissing

/-- Reflect the rotation order of a directed map with missing edges. The same
dart remains the tail of each present edge; the marked outer dart changes to
its opposite, in accordance with the orientation-reversing plane reflection -/
@[expose] def mirror (M : DirectedMapWithMissing D) : DirectedMapWithMissing D where
  toCombinatorialMap := M.toCombinatorialMap.mirror
  missing := M.missing
  missing_edgeInv := M.missing_edgeInv
  tail := M.tail
  tail_iff := M.tail_iff
  tail_missing := M.tail_missing
  outer := M.edgeInv M.outer
  missing_outer := by
    intro d hd
    rcases M.missing_outer d hd with h | h
    · right
      change M.toCombinatorialMap.mirror.faceSucc.SameCycle
        (M.edgeInv M.outer) (M.edgeInv d)
      simpa [M.toCombinatorialMap.edgeInv_invol] using
        (CombinatorialMap.faceMirrorSameCycle M.toCombinatorialMap
          M.outer d).2 h
    · left
      change M.toCombinatorialMap.mirror.faceSucc.SameCycle
        (M.edgeInv M.outer) d
      simpa [M.toCombinatorialMap.edgeInv_invol] using
        (CombinatorialMap.faceMirrorSameCycle M.toCombinatorialMap
          M.outer (M.edgeInv d)).2 h

/-- Outer-face membership in the reflected map is membership of the opposite
dart in the original map. -/
theorem mirror_isOuter_iff (M : DirectedMapWithMissing D) (d : D) :
    M.mirror.IsOuter d ↔ M.IsOuter (M.edgeInv d) := by
  change M.toCombinatorialMap.mirror.faceSucc.SameCycle
      (M.edgeInv M.outer) d ↔
    M.toCombinatorialMap.faceSucc.SameCycle M.outer (M.edgeInv d)
  simpa [M.toCombinatorialMap.edgeInv_invol] using
    (CombinatorialMap.faceMirrorSameCycle M.toCombinatorialMap M.outer
      (M.edgeInv d))

@[simp] private theorem vertexQuotientEquiv_mk (M : CombinatorialMap D) (d : D) :
    M.vertexQuotientEquiv
        (Quotient.mk (Equiv.Perm.SameCycle.setoid M.rot) d) =
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.mirror.rot) d := rfl

/-- The tail vertex is carried to the corresponding mirror vertex. Helper for -/
theorem mirror_dartTailVertex (M : DirectedMapWithMissing D) (d : D) :
    CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap
      (dartTailVertex M d) = dartTailVertex M.mirror d := by
  rfl

/-- The head vertex is carried to the corresponding mirror vertex. Helper for -/
theorem mirror_dartHeadVertex (M : DirectedMapWithMissing D) (d : D) :
    CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap
      (dartHeadVertex M d) = dartHeadVertex M.mirror d := by
  rfl

/-- The quotient equivalence with its codomain stated as a directed-map -/
@[expose] def mirrorVertexMap (M : DirectedMapWithMissing D) :
    MapVertex M → MapVertex M.mirror := fun v =>
  cast (show CombinatorialMap.VertexQuotient M.toCombinatorialMap.mirror =
    MapVertex M.mirror from rfl)
    (CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap v)

/-- Remove the vertex codomain cast in the reflection map. Helper toward
`prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirrorVertexMap_eq (M : DirectedMapWithMissing D) (v : MapVertex M) :
    mirrorVertexMap M v =
      CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap v := by
  rfl

/-- The reflection map is a bijection on vertices. Helper toward
`prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirrorVertexMap_bijective (M : DirectedMapWithMissing D) :
    Function.Bijective (mirrorVertexMap M) := by
  constructor
  · intro a b hab
    rw [mirrorVertexMap_eq, mirrorVertexMap_eq] at hab
    exact (CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap).injective hab
  · intro v
    obtain ⟨u, hu⟩ :=
      (CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap).surjective v
    exact ⟨u, (mirrorVertexMap_eq M u).trans hu⟩

private theorem mirrorVertexMap_dartVertices (M : DirectedMapWithMissing D) (d : D) :
    mirrorVertexMap M (dartTailVertex M d) = dartTailVertex M.mirror d ∧
      mirrorVertexMap M (dartHeadVertex M d) = dartHeadVertex M.mirror d := by
  constructor <;> rfl

namespace SimpleDirectedDartPath

/-- Transport a simple directed dart path through the mirror vertex
bijection, retaining its darts and orientation. Helper for `prop-uihbot-sym` -/
@[expose] def mirror {M : DirectedMapWithMissing D} {s t : MapVertex M}
    {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    SimpleDirectedDartPath M.mirror
      (mirrorVertexMap M s) (mirrorVertexMap M t) n where
  darts := P.darts
  vertices := P.vertices.map (mirrorVertexMap M)
  darts_length := P.darts_length
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map (by
    intro a b hab
    apply (CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap).injective
    simpa [mirrorVertexMap] using hab)
  start_vertex := by
    simpa [mirrorVertexMap] using congrArg (mirrorVertexMap M) P.start_vertex
  end_vertex := by
    simpa [mirrorVertexMap] using congrArg (mirrorVertexMap M) P.end_vertex
  edge_step := by
    intro i
    rcases P.edge_step i with ⟨hmiss, htail, htailV, hheadV⟩
    refine ⟨hmiss, htail, ?_, ?_⟩
    · calc
        _ = mirrorVertexMap M (P.vertices.get ⟨i.val, by
            have hi : i.val < n := by simpa [P.darts_length] using i.isLt
            rw [P.vertices_length]
            omega⟩) := by
          simp only [List.get_eq_getElem, List.getElem_map]
        _ = mirrorVertexMap M (dartTailVertex M (P.darts.get i)) :=
          congrArg (mirrorVertexMap M) htailV
        _ = dartTailVertex M.mirror (P.darts.get i) :=
          (mirrorVertexMap_dartVertices M (P.darts.get i)).1
    · calc
        _ = mirrorVertexMap M (P.vertices.get ⟨i.val + 1, by
            have hi : i.val < n := by simpa [P.darts_length] using i.isLt
            rw [P.vertices_length]
            omega⟩) := by
          simp only [List.get_eq_getElem, List.getElem_map]
        _ = mirrorVertexMap M (dartHeadVertex M (P.darts.get i)) :=
          congrArg (mirrorVertexMap M) hheadV
        _ = dartHeadVertex M.mirror (P.darts.get i) :=
          (mirrorVertexMap_dartVertices M (P.darts.get i)).2

end SimpleDirectedDartPath

/-- The directed edges are preserved under the vertex quotient equivalence. -/
theorem mirror_directedStep_iff (M : DirectedMapWithMissing D)
    (v w : CombinatorialMap.VertexQuotient M.toCombinatorialMap) :
    M.mirror.directedStep
        (CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap v)
        (CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap w) ↔
      M.directedStep v w := by
  unfold DirectedMapWithMissing.directedStep
  refine Quotient.inductionOn₂ v w ?_
  intro x y
  rw [vertexQuotientEquiv_mk, vertexQuotientEquiv_mk]
  constructor
  · rintro ⟨d, hmiss, htail, hstart, hend⟩
    refine ⟨d, hmiss, htail, ?_, ?_⟩
    · apply Quotient.sound
      exact Equiv.Perm.sameCycle_inv.mp (Quotient.exact hstart)
    · apply Quotient.sound
      exact Equiv.Perm.sameCycle_inv.mp (Quotient.exact hend)
  · rintro ⟨d, hmiss, htail, hstart, hend⟩
    refine ⟨d, hmiss, htail, ?_, ?_⟩
    · apply Quotient.sound
      exact Equiv.Perm.sameCycle_inv.mpr (Quotient.exact hstart)
    · apply Quotient.sound
      exact Equiv.Perm.sameCycle_inv.mpr (Quotient.exact hend)


/-- Directed steps expressed using the directed-map vertex transport. Helper
toward `prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirror_directedStep_iff' (M : DirectedMapWithMissing D)
    (v w : MapVertex M) :
    M.mirror.directedStep (mirrorVertexMap M v) (mirrorVertexMap M w) ↔
      M.directedStep v w := by
  rw [mirrorVertexMap_eq, mirrorVertexMap_eq]
  exact mirror_directedStep_iff M v w

private theorem transGen_mono_iff {α : Type*} {r s : α → α → Prop}
    (hrs : ∀ x y, r x y ↔ s x y) {a b : α} :
    Relation.TransGen r a b ↔ Relation.TransGen s a b := by
  constructor <;> intro h
  · exact Relation.TransGen.lift id (by
      intro x y hxy
      exact (hrs x y).mp hxy) a b h
  · exact Relation.TransGen.lift id (by
      intro x y hxy
      exact (hrs x y).mpr hxy) a b h

/-- Reversing the rotation order preserves directed acyclicity. -/
theorem mirror_isAcyclic_iff (M : DirectedMapWithMissing D) :
    M.mirror.IsAcyclic ↔ M.IsAcyclic := by
  let e := CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap
  constructor
  · intro h v hcycle
    apply h (e v)
    exact Relation.TransGen.lift e
      (by
        intro a b hab
        exact (mirror_directedStep_iff M a b).2 hab)
      v v hcycle
  · intro h v hcycle
    let v₀ := e.symm v
    have hv : e v₀ = v := e.apply_symm_apply v
    have hback : Relation.TransGen M.directedStep v₀ v₀ :=
      Relation.TransGen.lift e.symm
        (by
          intro a b hab
          have hab' : M.mirror.directedStep (e (e.symm a)) (e (e.symm b)) := by
            rw [e.apply_symm_apply, e.apply_symm_apply]
            exact hab
          exact (mirror_directedStep_iff M (e.symm a) (e.symm b)).1 hab')
        v v hcycle
    exact h v₀ hback

end DirectedMapWithMissing

namespace DirectedMapWithMissing

/-- The outer word of the mirror reverses its order and replaces each dart by -/
@[expose] def mirrorOuterWord (M : DirectedMapWithMissing D)
    (W : NonemptyWord D) : NonemptyWord D where
  letters := W.letters.reverse.map M.edgeInv
  nonempty := by
    intro hnil
    cases hletters : W.letters with
    | nil => exact (W.nonempty hletters).elim
    | cons a as => simp [hletters] at hnil
  nodup := List.Nodup.map M.toCombinatorialMap.edgeInv.injective
    (List.nodup_reverse.mpr W.nodup)

/-- Reflection exchanges the upper-left and lower-right outer darts while
leaving every edge orientation fixed. Helper for `prop-uihbot-sym` -/
theorem mirror_ul_lrDarts_iff (M : DirectedMapWithMissing D) (d : D) :
    (d ∈ M.mirror.ulDarts ↔ M.edgeInv d ∈ M.lrDarts) ∧
      (d ∈ M.mirror.lrDarts ↔ M.edgeInv d ∈ M.ulDarts) := by
  change (¬ M.missing d ∧ M.tail d ∧ M.mirror.IsOuter d ↔
      ¬ M.missing (M.edgeInv d) ∧ ¬ M.tail (M.edgeInv d) ∧
        M.IsOuter (M.edgeInv d)) ∧
    (¬ M.missing d ∧ ¬ M.tail d ∧ M.mirror.IsOuter d ↔
      ¬ M.missing (M.edgeInv d) ∧ M.tail (M.edgeInv d) ∧
        M.IsOuter (M.edgeInv d))
  constructor
  · constructor
    · rintro ⟨hmiss, htail, houter⟩
      refine ⟨?_, (M.tail_iff d hmiss).mp htail,
        (M.mirror_isOuter_iff d).mp houter⟩
      intro hm
      exact hmiss ((M.missing_edgeInv d).mpr hm)
    · rintro ⟨hmiss, htail, houter⟩
      have hmissD : ¬ M.missing d := by
        intro hm
        exact hmiss ((M.missing_edgeInv d).mp hm)
      refine ⟨hmissD, (M.tail_iff d hmissD).mpr htail,
        (M.mirror_isOuter_iff d).mpr houter⟩
  · constructor
    · rintro ⟨hmiss, hnotTail, houter⟩
      have hmissInv : ¬ M.missing (M.edgeInv d) := by
        intro hm
        exact hmiss ((M.missing_edgeInv d).mpr hm)
      have hmissD : ¬ M.missing d := by
        intro hm
        exact hmissInv ((M.missing_edgeInv d).mp hm)
      have htailInv : M.tail (M.edgeInv d) := by
        by_contra hn
        exact hnotTail ((M.tail_iff d hmissD).mpr hn)
      exact ⟨hmissInv, htailInv, (M.mirror_isOuter_iff d).mp houter⟩
    · rintro ⟨hmiss, htailInv, houter⟩
      have hmissD : ¬ M.missing d := by
        intro hm
        exact hmiss ((M.missing_edgeInv d).mp hm)
      refine ⟨hmissD, ?_, (M.mirror_isOuter_iff d).mpr houter⟩
      intro htail
      exact ((M.tail_iff d hmissD).mp htail) htailInv

end DirectedMapWithMissing

private theorem formPerm_map_perm (f : Equiv.Perm D) : ∀ xs : List D,
    (xs.map f).formPerm = f * xs.formPerm * f⁻¹
  | [] => by simp
  | [a] => by simp
  | a :: b :: xs => by
      have hswap : f * Equiv.swap a b * f⁻¹ = Equiv.swap (f a) (f b) := by
        ext x
        by_cases hxa : x = f a
        · subst x
          simp
        · by_cases hxb : x = f b
          · subst x
            simp
          · have hsa : f.symm x ≠ a := by
              intro h
              apply hxa
              calc
                x = f (f.symm x) := by simp
                _ = f a := congrArg f h
            have hsb : f.symm x ≠ b := by
              intro h
              apply hxb
              calc
                x = f (f.symm x) := by simp
                _ = f b := congrArg f h
            simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hxa, hxb, hsa, hsb]
      have hrec : (f b :: xs.map f).formPerm =
          f * (b :: xs).formPerm * f⁻¹ := by
        simpa only [List.map_cons] using formPerm_map_perm f (b :: xs)
      simp only [List.map_cons, List.formPerm_cons_cons]
      rw [hrec, ← hswap]
      simp [mul_assoc]

private theorem formPerm_reverse_map_perm (M : DirectedMapWithMissing D)
    (xs : List D) :
    (xs.reverse.map M.toCombinatorialMap.edgeInv).formPerm =
      M.toCombinatorialMap.edgeInv * xs.formPerm⁻¹ *
        M.toCombinatorialMap.edgeInv := by
  rw [formPerm_map_perm, List.formPerm_reverse]
  have hinv : M.toCombinatorialMap.edgeInv⁻¹ = M.toCombinatorialMap.edgeInv := by
    ext d
    apply M.toCombinatorialMap.edgeInv.injective
    simp [M.toCombinatorialMap.edgeInv_invol]
  rw [hinv]

/-- Reversing a permutation cycle preserves its exact three-step period. -/
theorem inverse_three_cycle (f : Equiv.Perm D) (x : D)
    (h3 : f (f (f x)) = x) (h1 : f x ≠ x) (h2 : f (f x) ≠ x) :
    f⁻¹ (f⁻¹ (f⁻¹ x)) = x ∧ f⁻¹ x ≠ x ∧ f⁻¹ (f⁻¹ x) ≠ x := by
  have hInv1 : f⁻¹ x ≠ x := by
    intro h
    apply h1
    have hh := congrArg f h
    simpa using hh.symm
  have hInv2 : f⁻¹ (f⁻¹ x) ≠ x := by
    intro h
    apply h2
    have hh := congrArg (fun y => f (f y)) h
    simpa [Equiv.Perm.mul_apply] using hh.symm
  have hInv3 : f⁻¹ (f⁻¹ (f⁻¹ x)) = x := by
    change f.symm (f.symm (f.symm x)) = x
    apply f.injective
    apply f.injective
    apply f.injective
    simpa only [Equiv.apply_symm_apply] using h3.symm
  exact ⟨hInv3, hInv1, hInv2⟩

namespace DirectedMapWithMissing

/-- The reversed opposite-dart word enumerates the mirror outer face with its -/
theorem mirror_isOuterCycle (M : DirectedMapWithMissing D) (W : NonemptyWord D)
    (hW : IsOuterCycle M W) :
    IsOuterCycle M.mirror (M.mirrorOuterWord W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases List.mem_map.mp (by simpa [mirrorOuterWord] using hd) with
      ⟨a, ha, rfl⟩
    apply (M.mirror_isOuter_iff (M.edgeInv a)).2
    simpa [M.toCombinatorialMap.edgeInv_invol] using
      (mem_iff_isOuter M W hW a).1 ha
  · intro d hd
    have houter : M.IsOuter (M.edgeInv d) := (M.mirror_isOuter_iff d).1 hd
    have hmem : M.edgeInv d ∈ W.letters :=
      (mem_iff_isOuter M W hW (M.edgeInv d)).2 houter
    apply List.mem_map.mpr
    refine ⟨M.edgeInv d, ?_, ?_⟩
    · simpa using hmem
    · simp [M.toCombinatorialMap.edgeInv_invol]
  · intro d hd
    rcases List.mem_map.mp (by simpa [mirrorOuterWord] using hd) with
      ⟨a, ha, rfl⟩
    have haOuter : M.IsOuter a := (mem_iff_isOuter M W hW a).1 ha
    have hpredOuter : M.IsOuter (M.toCombinatorialMap.faceSucc⁻¹ a) := by
      change M.toCombinatorialMap.faceSucc.SameCycle M.outer
        (M.toCombinatorialMap.faceSucc⁻¹ a)
      exact Equiv.Perm.sameCycle_symm_apply_right.mpr haOuter
    have hpredMem : M.toCombinatorialMap.faceSucc⁻¹ a ∈ W.letters :=
      (mem_iff_isOuter M W hW (M.toCombinatorialMap.faceSucc⁻¹ a)).2 hpredOuter
    have hpredStep := hW.2.2 _ hpredMem
    have hpredForm : W.letters.formPerm (M.toCombinatorialMap.faceSucc⁻¹ a) = a := by
      simpa using hpredStep.symm
    have hpredEq : W.letters.formPerm⁻¹ a = M.toCombinatorialMap.faceSucc⁻¹ a := by
      apply W.letters.formPerm.injective
      simpa using hpredForm.symm
    calc
      M.mirror.toCombinatorialMap.faceSucc (M.edgeInv a) =
          M.edgeInv (M.toCombinatorialMap.faceSucc⁻¹ a) := by
        change M.toCombinatorialMap.mirror.faceSucc (M.edgeInv a) =
          M.edgeInv (M.toCombinatorialMap.faceSucc⁻¹ a)
        rw [CombinatorialMap.mirror_faceSucc]
        simp [Equiv.Perm.mul_apply, M.toCombinatorialMap.edgeInv_invol]
      _ = M.edgeInv (W.letters.formPerm⁻¹ a) := by rw [hpredEq]
      _ = (M.mirrorOuterWord W).letters.formPerm (M.edgeInv a) := by
        have hword := formPerm_reverse_map_perm M W.letters
        have h := congrArg (fun p : Equiv.Perm D => p (M.edgeInv a)) hword
        simpa [mirrorOuterWord, Equiv.Perm.mul_apply,
          M.toCombinatorialMap.edgeInv_invol] using h.symm

/-- Reflection exchanges the two present boundary arcs. Helper toward
`prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirror_fourArcsWitness (M : DirectedMapWithMissing D)
    (W : NonemptyWord D) (L R : List D)
    (h : FourArcsWitness M W L [] (R.reverse.map M.edgeInv) []) :
    FourArcsWitness M.mirror (M.mirrorOuterWord W) R []
      (L.reverse.map M.edgeInv) [] := by
  rcases h with ⟨hcycle, hrot, hul, hlr, _, _⟩
  refine ⟨mirror_isOuterCycle M W hcycle, ?_, ?_, ?_, ?_, ?_⟩
  · have hr := hrot.reverse.map M.edgeInv
    simpa [mirrorOuterWord, List.reverse_append, List.map_append,
      List.map_reverse, List.map_map, Function.comp_def,
      M.toCombinatorialMap.edgeInv_invol] using hr
  · intro d
    rw [(mirror_ul_lrDarts_iff M d).1, ← hlr (M.edgeInv d)]
    constructor
    · intro hd
      exact List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
    · intro hd
      rcases List.mem_map.mp hd with ⟨a, ha, hea⟩
      have had : a = d := M.toCombinatorialMap.edgeInv.injective hea
      simpa [had] using ha
  · intro d
    rw [(mirror_ul_lrDarts_iff M d).2, ← hul (M.edgeInv d)]
    constructor
    · intro hd
      rcases List.mem_map.mp hd with ⟨a, ha, rfl⟩
      simpa [M.toCombinatorialMap.edgeInv_invol] using ha
    · intro hd
      exact List.mem_map.mpr ⟨M.edgeInv d, List.mem_reverse.mpr hd,
        M.toCombinatorialMap.edgeInv_invol d⟩
  · intro d hd
    simp at hd
  · intro d hd
    simp at hd

/-- Reflection preserves triangular inner faces by conjugating inverse face
cycles. Helper toward `prop-uihbot-sym` and the inverse of the restricted -/
theorem mirror_innerFacesDegreeThree (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.IsOuter d →
      M.toCombinatorialMap.faceSucc
          (M.toCombinatorialMap.faceSucc (M.toCombinatorialMap.faceSucc d)) = d ∧
        M.toCombinatorialMap.faceSucc d ≠ d ∧
        M.toCombinatorialMap.faceSucc (M.toCombinatorialMap.faceSucc d) ≠ d) :
    ∀ d, ¬ M.mirror.IsOuter d →
      M.mirror.toCombinatorialMap.faceSucc
          (M.mirror.toCombinatorialMap.faceSucc
            (M.mirror.toCombinatorialMap.faceSucc d)) = d ∧
        M.mirror.toCombinatorialMap.faceSucc d ≠ d ∧
        M.mirror.toCombinatorialMap.faceSucc
          (M.mirror.toCombinatorialMap.faceSucc d) ≠ d := by
  intro d hd
  have ho : ¬ M.IsOuter (M.edgeInv d) :=
    fun ho => hd ((mirror_isOuter_iff M d).mpr ho)
  obtain ⟨h3, h1, h2⟩ := h (M.edgeInv d) ho
  obtain ⟨hi3, hi1, hi2⟩ :=
    inverse_three_cycle M.toCombinatorialMap.faceSucc (M.edgeInv d) h3 h1 h2
  have hf (x : D) : M.mirror.toCombinatorialMap.faceSucc x =
      M.edgeInv (M.toCombinatorialMap.faceSucc⁻¹ (M.edgeInv x)) := by
    change M.toCombinatorialMap.mirror.faceSucc x = _
    rw [CombinatorialMap.mirror_faceSucc]
    rfl
  simp only [hf, M.toCombinatorialMap.edgeInv_invol]
  refine ⟨?_, ?_, ?_⟩
  · rw [hi3, M.toCombinatorialMap.edgeInv_invol]
  · intro heq
    apply hi1
    have he := congrArg M.edgeInv heq
    simpa only [M.toCombinatorialMap.edgeInv_invol] using he
  · intro heq
    apply hi2
    have he := congrArg M.edgeInv heq
    simpa only [M.toCombinatorialMap.edgeInv_invol] using he

/-- Reflecting a directed map twice restores its marked dart and all its
data. Helper toward `prop-uihbot-sym` and the inverse of the restricted -/
theorem mirror_mirror (M : DirectedMapWithMissing D) :
    M.mirror.mirror = M := by
  cases M with
  | mk C missing hm tail ht htm outer ho =>
    simp only [mirror, CombinatorialMap.mirror, C.edgeInv_invol]
    rfl

end DirectedMapWithMissing

namespace BipolarTriangulationWithBoundary

open DirectedMapWithMissing

/-- Reflect a bipolar triangulation, exchanging its left and right boundary
paths while preserving all arrows. Helper toward `prop-uihbot-sym` and the
inverse of the restricted boundary reversal -/
@[expose] noncomputable def mirror {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    BipolarTriangulationWithBoundary D r ℓ where
  map := B.map.mirror
  noMissingDarts := B.noMissingDarts
  planar := (CombinatorialMap.isPlanar_mirror_iff _).mpr B.planar
  innerFacesDegreeThree := mirror_innerFacesDegreeThree B.map B.innerFacesDegreeThree
  acyclic := (mirror_isAcyclic_iff B.map).mpr B.acyclic
  source := mirrorVertexMap B.map B.source
  sink := mirrorVertexMap B.map B.sink
  isSource := by
    rintro ⟨u, hu⟩
    obtain ⟨u₀, rfl⟩ := (mirrorVertexMap_bijective B.map).surjective u
    exact B.isSource ⟨u₀, (mirror_directedStep_iff' B.map u₀ B.source).mp hu⟩
  source_unique := by
    intro v hv
    obtain ⟨v₀, rfl⟩ := (mirrorVertexMap_bijective B.map).surjective v
    apply congrArg (mirrorVertexMap B.map)
    apply B.source_unique v₀
    rintro ⟨u, hu⟩
    exact hv ⟨mirrorVertexMap B.map u, (mirror_directedStep_iff' B.map u v₀).mpr hu⟩
  isSink := by
    rintro ⟨w, hw⟩
    obtain ⟨w₀, rfl⟩ := (mirrorVertexMap_bijective B.map).surjective w
    exact B.isSink ⟨w₀, (mirror_directedStep_iff' B.map B.sink w₀).mp hw⟩
  sink_unique := by
    intro v hv
    obtain ⟨v₀, rfl⟩ := (mirrorVertexMap_bijective B.map).surjective v
    apply congrArg (mirrorVertexMap B.map)
    apply B.sink_unique v₀
    rintro ⟨w, hw⟩
    exact hv ⟨mirrorVertexMap B.map w, (mirror_directedStep_iff' B.map v₀ w).mpr hw⟩
  left_length_pos := B.right_length_pos
  right_length_pos := B.left_length_pos
  outerWord := mirrorOuterWord B.map B.outerWord
  leftPath := DirectedMapWithMissing.SimpleDirectedDartPath.mirror B.rightPath
  rightPath := DirectedMapWithMissing.SimpleDirectedDartPath.mirror B.leftPath
  paths_internally_vertex_disjoint := by
    intro v hvR hvL
    change v ∈ B.rightPath.vertices.map (mirrorVertexMap B.map) at hvR
    change v ∈ B.leftPath.vertices.map (mirrorVertexMap B.map) at hvL
    obtain ⟨vR, hrmem, rfl⟩ := List.mem_map.mp hvR
    obtain ⟨vL, hlmem, heq⟩ := List.mem_map.mp hvL
    have heq' : vL = vR := (mirrorVertexMap_bijective B.map).injective heq
    subst vL
    rcases B.paths_internally_vertex_disjoint vR hlmem hrmem with h | h
    · exact Or.inl (congrArg (mirrorVertexMap B.map) h)
    · exact Or.inr (congrArg (mirrorVertexMap B.map) h)
  paths_edge_disjoint := by
    intro d hd e he hcycle
    exact B.paths_edge_disjoint e he d hd hcycle.symm
  outerSplit := mirror_fourArcsWitness B.map B.outerWord
    B.leftPath.darts B.rightPath.darts B.outerSplit

/-- Two reflections restore the directed map. Helper toward
`prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirror_mirror_map {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    B.mirror.mirror.map = B.map := by
  exact DirectedMapWithMissing.mirror_mirror B.map

/-- Two reflections restore the left boundary dart list. Helper toward
`prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirror_mirror_leftPath_darts {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    B.mirror.mirror.leftPath.darts = B.leftPath.darts := by
  rfl

/-- Two reflections restore the right boundary dart list. Helper toward
`prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirror_mirror_rightPath_darts {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    B.mirror.mirror.rightPath.darts = B.rightPath.darts := by
  rfl

/-- Reflection carries exactly the boundary vertices to boundary vertices.
Helper toward `prop-uihbot-sym` and the inverse of the restricted boundary -/
theorem mirror_mem_boundaryVertices_iff {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (v : MapVertex B.map) :
    mirrorVertexMap B.map v ∈ B.mirror.boundaryVertices ↔
      v ∈ B.boundaryVertices := by
  change (mirrorVertexMap B.map v ∈ B.rightPath.vertices.map (mirrorVertexMap B.map) ∨
    mirrorVertexMap B.map v ∈ B.leftPath.vertices.map (mirrorVertexMap B.map)) ↔
    (v ∈ B.leftPath.vertices ∨ v ∈ B.rightPath.vertices)
  rw [List.mem_map_of_injective (mirrorVertexMap_bijective B.map).injective,
    List.mem_map_of_injective (mirrorVertexMap_bijective B.map).injective, or_comm]

/-- Reflection preserves the set of boundary edge orbits. Helper toward
`prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirror_boundaryEdge_iff {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundary D ℓ r) (d : D) :
    B.mirror.boundaryEdge d ↔ B.boundaryEdge d := by
  change (∃ e ∈ B.rightPath.darts ++ B.leftPath.darts,
    Equiv.Perm.SameCycle B.map.edgeInv d e) ↔
    (∃ e ∈ B.leftPath.darts ++ B.rightPath.darts,
      Equiv.Perm.SameCycle B.map.edgeInv d e)
  simp only [List.mem_append]
  constructor <;> rintro ⟨e, he, hcycle⟩ <;>
    exact ⟨e, he.elim Or.inr Or.inl, hcycle⟩

/-- Boundary channeling is preserved by reflection: arrows and edge orbits
are retained and the boundary sides are exchanged. Helper toward
`prop-uihbot-sym` and the inverse of the restricted boundary reversal -/
theorem mirror_isBoundaryChanneled {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundary D ℓ r}
    (hbc : B.IsBoundaryChanneled) : B.mirror.IsBoundaryChanneled := by
  intro d hmiss htail hboundary hneq
  apply (mirror_boundaryEdge_iff B d).mpr
  apply hbc d hmiss htail
  · apply (mirror_mem_boundaryVertices_iff B (dartHeadVertex B.map d)).mp
    rw [(mirrorVertexMap_dartVertices B.map d).2]
    exact hboundary
  · intro heq
    apply hneq
    change dartHeadVertex B.map.mirror d = mirrorVertexMap B.map B.sink
    rw [← (mirrorVertexMap_dartVertices B.map d).2, heq]

end BipolarTriangulationWithBoundary

end DirectedDistances.PlanarMap
