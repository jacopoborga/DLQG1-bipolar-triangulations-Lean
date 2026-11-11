module

public import DirectedDistances.PlanarMap.PlanarPathGlueBase

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PlanarMap

open Relation

private abbrev pathVertex {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (i : Fin (n + 1)) : MapVertex M :=
  P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩

private theorem pathVertex_step {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (i : ℕ) (hi : i < n) :
    M.directedStep (pathVertex P ⟨i, by omega⟩)
      (pathVertex P ⟨i + 1, by omega⟩) := by
  let k : Fin P.darts.length := ⟨i, by rw [P.darts_length]; exact hi⟩
  obtain ⟨hm, ht, hv, hw⟩ := P.edge_step k
  exact ⟨P.darts.get k, hm, ht, hv.symm, hw.symm⟩

private theorem pathVertex_forward {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (i j : Fin (n + 1))
    (hij : i.val < j.val) :
    TransGen M.directedStep (pathVertex P i) (pathVertex P j) := by
  have aux : ∀ k, i.val + 1 ≤ k → ∀ hk : k < n + 1,
      TransGen M.directedStep (pathVertex P i) (pathVertex P ⟨k, hk⟩) := by
    intro k h
    induction k, h using Nat.le_induction with
    | base =>
      intro hk
      exact TransGen.single (pathVertex_step P i.val (by omega))
    | succ k h ih =>
      intro hk
      exact (ih (by omega)).tail (pathVertex_step P k (by omega))
  exact aux j.val hij j.isLt

private theorem pathVertex_index_lt {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {a b : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M a b n) (hM : M.IsAcyclic)
    (i j : Fin (n + 1))
    (h : TransGen M.directedStep (pathVertex P i) (pathVertex P j)) :
    i.val < j.val := by
  by_contra hn
  by_cases he : i = j
  · subst j
    exact hM _ h
  · have hji : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
      omega
    exact hM _ (h.trans (pathVertex_forward P j i hji))

private theorem seam_reach_lifts
    {X Y V I : Type*} {A : X → X → Prop} {B : Y → Y → Prop}
    {C : V → V → Prop} (f : X → V) (g : Y → V)
    (lf : I → X) (rg : I → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hcross : ∀ x y, f x = g y ↔ ∃ i, x = lf i ∧ y = rg i)
    (hstep : ∀ u v, C u v →
      (∃ x y, A x y ∧ f x = u ∧ f y = v) ∨
      (∃ x y, B x y ∧ g x = u ∧ g y = v))
    (hseam : ∀ i j, TransGen B (rg i) (rg j) → TransGen A (lf i) (lf j))
    {u v : V} (h : TransGen C u v) :
    ∀ a, f a = u →
      (∀ b, f b = v → TransGen A a b) ∧
      (∀ b, g b = v → ∃ i, ReflTransGen A a (lf i) ∧
        ReflTransGen B (rg i) b) := by
  induction h with
  | single huv =>
    intro a ha
    rcases hstep _ _ huv with ⟨x, y, hxy, hx, hy⟩ | ⟨x, y, hxy, hx, hy⟩
    · have hax := hf (ha.trans hx.symm)
      subst x
      constructor
      · intro b hb
        have hby := hf (hb.trans hy.symm)
        subst b
        exact TransGen.single hxy
      · intro b hb
        obtain ⟨i, hi, hb'⟩ := (hcross y b).mp (hy.trans hb.symm)
        subst y
        subst b
        exact ⟨i, ReflTransGen.single hxy, ReflTransGen.refl⟩
    · obtain ⟨i, hi, hx'⟩ := (hcross a x).mp (ha.trans hx.symm)
      subst a
      subst x
      constructor
      · intro b hb
        obtain ⟨j, hb', hy'⟩ := (hcross b y).mp (hb.trans hy.symm)
        subst b
        subst y
        exact hseam i j (TransGen.single hxy)
      · intro b hb
        have hby := hg (hb.trans hy.symm)
        subst b
        exact ⟨i, ReflTransGen.refl, ReflTransGen.single hxy⟩
  | tail huv hvw ih =>
    intro a ha
    obtain ⟨hL, hR⟩ := ih a ha
    rcases hstep _ _ hvw with ⟨x, y, hxy, hx, hy⟩ | ⟨x, y, hxy, hx, hy⟩
    · have hax := hL x hx
      constructor
      · intro b hb
        have hby := hf (hb.trans hy.symm)
        subst b
        exact hax.tail hxy
      · intro b hb
        obtain ⟨i, hi, hb'⟩ := (hcross y b).mp (hy.trans hb.symm)
        subst y
        subst b
        exact ⟨i, (hax.tail hxy).to_reflTransGen, ReflTransGen.refl⟩
    · obtain ⟨i, hai, hix⟩ := hR x hx
      constructor
      · intro b hb
        obtain ⟨j, hb', hy'⟩ := (hcross b y).mp (hb.trans hy.symm)
        subst b
        subst y
        exact TransGen.trans_right hai (hseam i j (TransGen.tail' hix hxy))
      · intro b hb
        have hby := hg (hb.trans hy.symm)
        subst b
        exact ⟨i, hai, hix.tail hxy⟩

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)

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

private abbrev leftSeam (i : Fin (s + 1)) : MapVertex BL.map :=
  dartTailVertex BL.map (glueLeftSeamVertexDart BL i)

private abbrev rightSeam (i : Fin (s + 1)) : MapVertex BR.map :=
  dartTailVertex BR.map (glueRightSeamVertexDart BR i)

private theorem seam_transfer_left (i j : Fin (s + 1))
    (h : TransGen BR.map.directedStep (rightSeam BR i) (rightSeam BR j)) :
    TransGen BL.map.directedStep (leftSeam BL i) (leftSeam BL j) := by
  simp only [rightSeam, glueRightSeamVertexDart_vertex] at h
  have hij := pathVertex_index_lt BR.leftPath BR.acyclic i j h
  simpa only [leftSeam, glueLeftSeamVertexDart_vertex] using
    pathVertex_forward BL.rightPath i j hij

private theorem seam_transfer_right (i j : Fin (s + 1))
    (h : TransGen BL.map.directedStep (leftSeam BL i) (leftSeam BL j)) :
    TransGen BR.map.directedStep (rightSeam BR i) (rightSeam BR j) := by
  simp only [leftSeam, glueLeftSeamVertexDart_vertex] at h
  have hij := pathVertex_index_lt BL.rightPath BL.acyclic i j h
  simpa only [rightSeam, glueRightSeamVertexDart_vertex] using
    pathVertex_forward BR.leftPath i j hij



theorem glue_isAcyclic : (glueDirectedMap BL BR).IsAcyclic := by
  let f : MapVertex BL.map → MapVertex (glueDirectedMap BL BR) :=
    fun a => glueDirectedVertexMap BL BR (.inl a)
  let g : MapVertex BR.map → MapVertex (glueDirectedMap BL BR) :=
    fun b => glueDirectedVertexMap BL BR (.inr b)
  have hf : Function.Injective f := fun _ _ h =>
    glueVertexMap_left_injective BL BR ((directed_vertex_eq BL BR _ _).mp h)
  have hg : Function.Injective g := fun _ _ h =>
    glueVertexMap_right_injective BL BR ((directed_vertex_eq BL BR _ _).mp h)
  have hc : ∀ a b, f a = g b ↔ ∃ i, a = leftSeam BL i ∧ b = rightSeam BR i := by
    intro a b
    exact (directed_vertex_eq BL BR _ _).trans (glueVertexMap_cross_iff BL BR a b)
  have hs : ∀ u v, (glueDirectedMap BL BR).directedStep u v →
      (∃ a b, BL.map.directedStep a b ∧ f a = u ∧ f b = v) ∨
      (∃ a b, BR.map.directedStep a b ∧ g a = u ∧ g b = v) := by
    intro u v h
    exact (glue_directedStep_iff BL BR u v).mp h
  intro v hcycle
  have hv : ∃ x, glueDirectedVertexMap BL BR x = v := by
    refine Quotient.inductionOn v ?_
    intro d
    obtain ⟨d | d, rfl⟩ := glueIdentify_surjective BL BR d
    · exact ⟨.inl (dartTailVertex BL.map d), rfl⟩
    · exact ⟨.inr (dartTailVertex BR.map d), rfl⟩
  obtain ⟨a | b, hv⟩ := hv
  · obtain ⟨hL, _⟩ := seam_reach_lifts f g (leftSeam BL) (rightSeam BR)
      hf hg hc hs (seam_transfer_left BL BR) hcycle a hv
    exact BL.acyclic a (hL a hv)
  · have hc' : ∀ b a, g b = f a ↔ ∃ i, b = rightSeam BR i ∧ a = leftSeam BL i := by
      intro b a
      constructor
      · intro h
        obtain ⟨i, ha, hb⟩ := (hc a b).mp h.symm
        exact ⟨i, hb, ha⟩
      · rintro ⟨i, hb, ha⟩
        exact ((hc a b).mpr ⟨i, ha, hb⟩).symm
    have hs' : ∀ u v, (glueDirectedMap BL BR).directedStep u v →
        (∃ a b, BR.map.directedStep a b ∧ g a = u ∧ g b = v) ∨
        (∃ a b, BL.map.directedStep a b ∧ f a = u ∧ f b = v) := by
      intro u v h
      exact (hs u v h).symm
    obtain ⟨hR, _⟩ := seam_reach_lifts g f (rightSeam BR) (leftSeam BL)
      hg hf hc' hs' (seam_transfer_right BL BR) hcycle b hv
    exact BR.acyclic b (hR b hv)



@[expose] noncomputable def glueBase :
    BipolarTriangulationWithBoundaryBase (GlueDart BL BR) ℓ r where
  map := glueDirectedMap BL BR
  noMissingDarts := glueDirectedMap_noMissing BL BR
  planar := by rw [glueDirectedMap_toCombinatorialMap]; exact glue_isPlanar BL BR
  innerFacesDegreeThree := by
    intro d hd
    rw [glueDirectedMap_toCombinatorialMap]
    exact glue_innerFacesDegreeThree BL BR d hd
  acyclic := glue_isAcyclic BL BR
  source := glueDirectedVertexMap BL BR (.inl BL.source)
  sink := glueDirectedVertexMap BL BR (.inl BL.sink)
  isSource := glue_isSource BL BR
  source_unique := glue_source_unique BL BR
  isSink := glue_isSink BL BR
  sink_unique := glue_sink_unique BL BR
  left_length_pos := BL.left_length_pos
  right_length_pos := BR.right_length_pos
  outerWord := glueOuterWord BL BR
  leftPath := glueLeftPath BL BR
  rightPath := glueRightPath BL BR
  outerSplit := glue_outerSplit BL BR

 
@[simp] theorem glueBase_map : (glueBase BL BR).map = glueDirectedMap BL BR := rfl

 
@[simp] theorem glueBase_source : (glueBase BL BR).source =
    glueDirectedVertexMap BL BR (.inl BL.source) := rfl

 
@[simp] theorem glueBase_sink : (glueBase BL BR).sink =
    glueDirectedVertexMap BL BR (.inl BL.sink) := rfl

 
@[simp] theorem glueBase_leftPath_darts : (glueBase BL BR).leftPath.darts =
    BL.leftPath.darts.map (fun d => glueIdentify BL BR (.inl d)) := rfl

 
@[simp] theorem glueBase_rightPath_darts : (glueBase BL BR).rightPath.darts =
    BR.rightPath.darts.map (fun d => glueIdentify BL BR (.inr d)) := rfl



theorem glueBase_numEdges :
    (glueBase BL BR).map.toCombinatorialMap.numEdges + s =
      BL.map.toCombinatorialMap.numEdges + BR.map.toCombinatorialMap.numEdges := by
  rw [glueBase_map, glueDirectedMap_toCombinatorialMap]
  exact numEdges_glueCombinatorialMap BL BR

end DirectedDistances.PlanarMap
