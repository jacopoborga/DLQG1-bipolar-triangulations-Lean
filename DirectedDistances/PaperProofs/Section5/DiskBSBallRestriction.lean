module

public import DirectedDistances.PaperProofs.Section5.DiskBSBallLaw
import DirectedDistances.PlanarMap.CombinatorialMapEulerBound

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result.
Every map on framed-ball classes is measurable for the top measurable spaces -/
theorem measurable_framedBallClass_map
    (f : FramedBallClass → FramedBallClass) :
    Measurable f := by
  intro s hs
  exact MeasurableSpace.measurableSet_top

/-- Every path of length at most `r'` from the stage-ball center stays in the
Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem kmswStageDistanceLe_iff_pathWithinBall
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r r' c v : ℕ)
    (hrr : r' ≤ r) (hc : c < (kmswStage w n).nextVertex) :
    kmswStageDistanceLe P (kmswStage w n) r' c v ↔
      ∃ k, k ≤ r' ∧ KMSWStagePath P (kmswStage w n)
        (↑(kmswStageBallVertices P (kmswStage w n) r c)) c k v := by
  constructor
  · rintro ⟨k, hk, hpath⟩
    refine ⟨k, hk, ?_⟩
    apply kmswStagePathIn_of_distanceClosed P (kmswStage w n)
      (↑(kmswStageBallVertices P (kmswStage w n) r c)) r c ?_ hpath
      (le_trans hk hrr)
    intro x hx
    exact (kmswStageBallVertices_mem_iff_distanceLe P w n r c x hc).2 hx
  · rintro ⟨k, hk, hpath⟩
    exact ⟨k, hk, kmswStagePathForgetVertices P (kmswStage w n)
      (↑(kmswStageBallVertices P (kmswStage w n) r c)) hpath⟩

/-- The inner stage-ball dart carrier is characterized by short paths for both
Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem kmswStageBallDarts_mem_iff_pathsWithinBall
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r r' c : ℕ)
    (hrr : r' ≤ r) (hc : c < (kmswStage w n).nextVertex)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageBallDarts P (kmswStage w n) r' c ↔
      (∃ k, k ≤ r' ∧ KMSWStagePath P (kmswStage w n)
        (↑(kmswStageBallVertices P (kmswStage w n) r c)) c k
        (stageEndpoint (kmswStage w n) d)) ∧
      (∃ k, k ≤ r' ∧ KMSWStagePath P (kmswStage w n)
        (↑(kmswStageBallVertices P (kmswStage w n) r c)) c k
        (stageEndpoint (kmswStage w n) (edgeFlip _ d))) := by
  rw [kmswStageBallDarts_mem_iff_distanceLe_endpoints P w n r' c hc d]
  exact and_congr
    (kmswStageDistanceLe_iff_pathWithinBall P w n r r' c _ hrr hc)
    (kmswStageDistanceLe_iff_pathWithinBall P w n r r' c _ hrr hc)

/-- The radius-`r'` stage darts are exactly the radius-`r` darts whose endpoints
are within radius `r'` by paths constrained to the radius-`r` vertices
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem kmswStageBallDarts_inner_iff_withinOuterBall
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r r' c : ℕ)
    (hrr : r' ≤ r) (hc : c < (kmswStage w n).nextVertex)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageBallDarts P (kmswStage w n) r' c ↔
      d ∈ kmswStageBallDarts P (kmswStage w n) r c ∧
        (∃ k, k ≤ r' ∧ KMSWStagePath P (kmswStage w n)
          (↑(kmswStageBallVertices P (kmswStage w n) r c)) c k
          (stageEndpoint (kmswStage w n) d)) ∧
        (∃ k, k ≤ r' ∧ KMSWStagePath P (kmswStage w n)
          (↑(kmswStageBallVertices P (kmswStage w n) r c)) c k
          (stageEndpoint (kmswStage w n) (edgeFlip _ d))) := by
  constructor
  · intro hd
    have hpaths :=
      (kmswStageBallDarts_mem_iff_pathsWithinBall P w n r r' c hrr hc d).mp hd
    exact ⟨kmswStageBallDarts_mono P (kmswStage w n) hrr hd, hpaths.1,
      hpaths.2⟩
  · rintro ⟨_, hstart, hfinish⟩
    exact (kmswStageBallDarts_mem_iff_pathsWithinBall P w n r r' c hrr hc d).2
      ⟨hstart, hfinish⟩

/-- The inner stage-ball dart carrier is contained in the outer one
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem kmswStageBallDarts_inner_subset
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r r' c : ℕ)
    (hrr : r' ≤ r) :
    kmswStageBallDarts P (kmswStage w n) r' c ⊆
      kmswStageBallDarts P (kmswStage w n) r c :=
  kmswStageBallDarts_mono P (kmswStage w n) hrr

/-- The edge involution of a first restriction preserves the nested dart set
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem inducedCombinatorialMap_nested_edgeInv_closed
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S T : Finset D)
    (hflipS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hflipT : ∀ d, d ∈ T → M.edgeInv d ∈ T) :
    ∀ x : {d : D // d ∈ S},
      x ∈ firstReturnSubset S T →
        (inducedCombinatorialMap M S hflipS).edgeInv x ∈
          firstReturnSubset S T := by
  classical
  intro x hx
  simp only [firstReturnSubset, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx ⊢
  have hval : ((inducedCombinatorialMap M S hflipS).edgeInv x).1 =
      M.edgeInv x.1 := by
    simp [inducedCombinatorialMap]
  rw [hval]
  exact hflipT x.1 hx

/-- Restricting a first-return combinatorial map twice has the same rotation
as restricting directly to the smaller dart set
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem inducedCombinatorialMap_nested_rot_val
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S T : Finset D)
    (hflipS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hflipT : ∀ d, d ∈ T → M.edgeInv d ∈ T)
    (hTS : ∀ d, d ∈ T → d ∈ S)
    (d : {d : D // d ∈ T}) :
    ((inducedCombinatorialMap
        (inducedCombinatorialMap M S hflipS)
        (firstReturnSubset S T)
        (inducedCombinatorialMap_nested_edgeInv_closed M S T hflipS hflipT)).rot
      ⟨⟨d.1, hTS d.1 d.2⟩,
        by simp [firstReturnSubset, d.2]⟩).val.val =
      ((inducedCombinatorialMap M T hflipT).rot d).val := by
  classical
  let hperS := finitePermutationReturn M.rot S
  let R := cyclicFirstReturn M.rot S hperS
  let U := firstReturnSubset S T
  let hperU := finitePermutationReturn R U
  let hperT := finitePermutationReturn M.rot T
  have h := firstReturn_nested' M.rot S T hperS hTS hperU hperT d
  simpa only [inducedCombinatorialMap_rot] using h

/-- The dart carrier of a nested first-return restriction is equivalent to the
toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
@[expose] def inducedCombinatorialMap_nestedDartEquiv
    {D : Type} [Fintype D] [DecidableEq D]
    (S T : Finset D) (hTS : ∀ d, d ∈ T → d ∈ S) :
    {x : {d : D // d ∈ S} // x ∈ firstReturnSubset S T} ≃
      {d : D // d ∈ T} where
  toFun x := ⟨x.1.1, by simpa [firstReturnSubset] using x.2⟩
  invFun x := ⟨⟨x.1, hTS x.1 x.2⟩, by simp [firstReturnSubset, x.2]⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The nested first-return rotation agrees under the dart equivalence with
Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem inducedCombinatorialMap_nested_rot_comm
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S T : Finset D)
    (hflipS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hflipT : ∀ d, d ∈ T → M.edgeInv d ∈ T)
    (hTS : ∀ d, d ∈ T → d ∈ S)
    (x : {x : {d : D // d ∈ S} // x ∈ firstReturnSubset S T}) :
    inducedCombinatorialMap_nestedDartEquiv S T hTS
        ((inducedCombinatorialMap
          (inducedCombinatorialMap M S hflipS)
          (firstReturnSubset S T)
          (inducedCombinatorialMap_nested_edgeInv_closed
            M S T hflipS hflipT)).rot x) =
      (inducedCombinatorialMap M T hflipT).rot
        (inducedCombinatorialMap_nestedDartEquiv S T hTS x) := by
  apply Subtype.ext
  exact inducedCombinatorialMap_nested_rot_val M S T hflipS hflipT hTS
    (inducedCombinatorialMap_nestedDartEquiv S T hTS x)

/-- The nested edge involution agrees under the dart equivalence with direct
5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem inducedCombinatorialMap_nested_edgeInv_comm
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S T : Finset D)
    (hflipS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hflipT : ∀ d, d ∈ T → M.edgeInv d ∈ T)
    (hTS : ∀ d, d ∈ T → d ∈ S)
    (x : {x : {d : D // d ∈ S} // x ∈ firstReturnSubset S T}) :
    inducedCombinatorialMap_nestedDartEquiv S T hTS
        ((inducedCombinatorialMap
          (inducedCombinatorialMap M S hflipS)
          (firstReturnSubset S T)
          (inducedCombinatorialMap_nested_edgeInv_closed
            M S T hflipS hflipT)).edgeInv x) =
      (inducedCombinatorialMap M T hflipT).edgeInv
        (inducedCombinatorialMap_nestedDartEquiv S T hTS x) := by
  apply Subtype.ext
  simp [inducedCombinatorialMap_nestedDartEquiv, inducedCombinatorialMap]

/-- Connectedness is preserved when a first-return restriction is nested
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem inducedCombinatorialMap_nested_isConnected
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S T : Finset D)
    (hflipS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hflipT : ∀ d, d ∈ T → M.edgeInv d ∈ T)
    (hTS : ∀ d, d ∈ T → d ∈ S)
    (hconnected : (inducedCombinatorialMap M T hflipT).IsConnected) :
    (inducedCombinatorialMap
      (inducedCombinatorialMap M S hflipS)
      (firstReturnSubset S T)
      (inducedCombinatorialMap_nested_edgeInv_closed M S T hflipS hflipT)).IsConnected := by
  classical
  let N := inducedCombinatorialMap
    (inducedCombinatorialMap M S hflipS)
    (firstReturnSubset S T)
    (inducedCombinatorialMap_nested_edgeInv_closed M S T hflipS hflipT)
  let R := inducedCombinatorialMap M T hflipT
  let E := inducedCombinatorialMap_nestedDartEquiv S T hTS
  have hrot (x : {x : {d : D // d ∈ S} // x ∈ firstReturnSubset S T}) :
      E (N.rot x) = R.rot (E x) :=
    inducedCombinatorialMap_nested_rot_comm M S T hflipS hflipT hTS x
  have hedge (x : {x : {d : D // d ∈ S} // x ∈ firstReturnSubset S T}) :
      E (N.edgeInv x) = R.edgeInv (E x) :=
    inducedCombinatorialMap_nested_edgeInv_comm M S T hflipS hflipT hTS x
  have hrotSymm (x : {d : D // d ∈ T}) :
      E (N.rot.symm (E.symm x)) = R.rot.symm x := by
    apply R.rot.injective
    rw [R.rot.apply_symm_apply]
    rw [← hrot]
    simp
  have hedgeSymm (x : {d : D // d ∈ T}) :
      E (N.edgeInv.symm (E.symm x)) = R.edgeInv.symm x := by
    apply R.edgeInv.injective
    rw [R.edgeInv.apply_symm_apply]
    rw [← hedge]
    simp
  have hstep (x y : {d : D // d ∈ T})
      (hs : y = R.rot x ∨ y = R.rot.symm x ∨
        y = R.edgeInv x ∨ y = R.edgeInv.symm x) :
      E.symm y = N.rot (E.symm x) ∨ E.symm y = N.rot.symm (E.symm x) ∨
        E.symm y = N.edgeInv (E.symm x) ∨
        E.symm y = N.edgeInv.symm (E.symm x) := by
    rcases hs with h | h | h | h
    · left
      apply E.injective
      calc
        E (E.symm y) = y := E.apply_symm_apply y
        _ = R.rot x := h
        _ = E (N.rot (E.symm x)) := by rw [hrot]; simp
    · right; left
      apply E.injective
      calc
        E (E.symm y) = y := E.apply_symm_apply y
        _ = R.rot.symm x := h
        _ = E (N.rot.symm (E.symm x)) := (hrotSymm x).symm
    · right; right; left
      apply E.injective
      calc
        E (E.symm y) = y := E.apply_symm_apply y
        _ = R.edgeInv x := h
        _ = E (N.edgeInv (E.symm x)) := by rw [hedge]; simp
    · right; right; right
      apply E.injective
      calc
        E (E.symm y) = y := E.apply_symm_apply y
        _ = R.edgeInv.symm x := h
        _ = E (N.edgeInv.symm (E.symm x)) := (hedgeSymm x).symm
  have hpull : ∀ x y : {d : D // d ∈ T},
      Relation.ReflTransGen
        (fun a b : {d : D // d ∈ T} =>
          b = R.rot a ∨ b = R.rot.symm a ∨
          b = R.edgeInv a ∨ b = R.edgeInv.symm a) x y →
      Relation.ReflTransGen
        (fun a b : {x : {d : D // d ∈ S} // x ∈ firstReturnSubset S T} =>
          b = N.rot a ∨ b = N.rot.symm a ∨
          b = N.edgeInv a ∨ b = N.edgeInv.symm a)
        (E.symm x) (E.symm y) := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstepR ih =>
      exact Relation.ReflTransGen.tail ih (hstep _ _ hstepR)
  intro x y
  have hpath := hpull (E x) (E y) (hconnected (E x) (E y))
  simpa using hpath

/-- The restriction of the radius-`r` stage ball to the radius-`r'` stage ball is
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem kmswDiskStageBall_nested_isConnected {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r r' : ℕ)
    (hr' : 0 < r') (hrr : r' ≤ r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let d := kmswDiskRootDart c k
    let Sbig := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r
      (stageEndpoint (kmswStage u n) (edgeFlip _ d))
    let Ssmall := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r'
      (stageEndpoint (kmswStage u n) (edgeFlip _ d))
    let hfBig := fun e he => (kmswStageBallDarts_edgeFlip
      (fun _ _ => True) (kmswStage u n) r
      (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he
    let hfSmall := fun e he => (kmswStageBallDarts_edgeFlip
      (fun _ _ => True) (kmswStage u n) r'
      (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he
    @CombinatorialMap.IsConnected _ _
      (@Subtype.instDecidableEq _ _ Subtype.instDecidableEq)
      (@inducedCombinatorialMap _ _ Subtype.instDecidableEq
        (inducedCombinatorialMap (kmswStageDirectedMap u n).toCombinatorialMap
          Sbig hfBig)
        (firstReturnSubset Sbig Ssmall)
        (inducedCombinatorialMap_nested_edgeInv_closed
          (kmswStageDirectedMap u n).toCombinatorialMap Sbig Ssmall
          hfBig hfSmall)) := by
  intro u d Sbig Ssmall hfBig hfSmall
  have hconn := kmswStageBallCombinatorialMap_rooted_isConnected u n r' d hr'
  have h := inducedCombinatorialMap_nested_isConnected
    (kmswStageDirectedMap u n).toCombinatorialMap Sbig Ssmall hfBig hfSmall
    (fun e he => kmswStageBallDarts_inner_subset (fun _ _ => True) u n r r' _ hrr he)
    hconn
  convert h

/-- Cycle membership is transported by a bijection intertwining two finite
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem sameCycle_map_of_intertwine {α β : Type} [Finite α]
    (f : Equiv.Perm α) (g : Equiv.Perm β) (E : α ≃ β)
    (h : ∀ x, E (f x) = g (E x)) {x y : α} (hxy : f.SameCycle x y) :
    g.SameCycle (E x) (E y) := by
  have hpow : ∀ (m : ℕ) (z : α), E ((f ^ m) z) = (g ^ m) (E z) := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply, ih, h]
  obtain ⟨j, hj⟩ := hxy.exists_nat_pow_eq
  refine ⟨(j : ℤ), ?_⟩
  rw [zpow_natCast, ← hpow, hj]

/-- Face-cycle membership agrees under a bijection intertwining the face
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem sameCycle_iff_of_intertwine {α β : Type} [Finite α] [Finite β]
    (f : Equiv.Perm α) (g : Equiv.Perm β) (E : α ≃ β)
    (h : ∀ x, E (f x) = g (E x)) (x y : α) :
    f.SameCycle x y ↔ g.SameCycle (E x) (E y) := by
  refine ⟨sameCycle_map_of_intertwine f g E h, fun hxy => ?_⟩
  have h' : ∀ z, E.symm (g z) = f (E.symm z) := by
    intro z
    apply E.injective
    rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]
  have := sameCycle_map_of_intertwine g f E.symm h' hxy
  simpa using this

/-- The nested first-return face permutation agrees under the dart equivalence with
Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem inducedCombinatorialMap_nested_faceSucc_comm
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S T : Finset D)
    (hflipS : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hflipT : ∀ d, d ∈ T → M.edgeInv d ∈ T)
    (hTS : ∀ d, d ∈ T → d ∈ S)
    (x : {x : {d : D // d ∈ S} // x ∈ firstReturnSubset S T}) :
    inducedCombinatorialMap_nestedDartEquiv S T hTS
        ((inducedCombinatorialMap
          (inducedCombinatorialMap M S hflipS)
          (firstReturnSubset S T)
          (inducedCombinatorialMap_nested_edgeInv_closed
            M S T hflipS hflipT)).faceSucc x) =
      (inducedCombinatorialMap M T hflipT).faceSucc
        (inducedCombinatorialMap_nestedDartEquiv S T hTS x) := by
  let N := inducedCombinatorialMap
    (inducedCombinatorialMap M S hflipS)
    (firstReturnSubset S T)
    (inducedCombinatorialMap_nested_edgeInv_closed M S T hflipS hflipT)
  let R := inducedCombinatorialMap M T hflipT
  let E := inducedCombinatorialMap_nestedDartEquiv S T hTS
  have hsymm (z : {x : {d : D // d ∈ S} // x ∈ firstReturnSubset S T}) :
      E (N.rot.symm z) = R.rot.symm (E z) := by
    apply R.rot.injective
    rw [Equiv.apply_symm_apply,
      ← inducedCombinatorialMap_nested_rot_comm M S T hflipS hflipT hTS]
    rw [Equiv.apply_symm_apply]
  change E (N.rot.symm (N.edgeInv x)) = R.rot.symm (R.edgeInv (E x))
  rw [hsymm, inducedCombinatorialMap_nested_edgeInv_comm M S T hflipS hflipT hTS]

private noncomputable def diskRestrictionEdgeExtension
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip)) : EdgeSpace M := by
  classical
  let N := inducedCombinatorialMap M S hflip
  refine fun q => Quotient.lift
    (fun d => if hd : d ∈ S then c (edgeClass N ⟨d, hd⟩) else 0) ?_ q
  intro d e hde
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M d e).mp hde with h | h
  · subst e
    rfl
  · subst e
    by_cases hd : d ∈ S
    · rw [dite_eq_left hd, dite_eq_left (hflip d hd)]
      apply congrArg c
      apply Quotient.sound
      exact (CombinatorialMap.edgeInv_sameCycle_iff N _ _).mpr (Or.inr rfl)
    · have hf : M.edgeInv d ∉ S := by
        intro h
        have hh := hflip (M.edgeInv d) h
        exact hd (by simpa only [M.edgeInv_invol] using hh)
      rw [dite_eq_right hd, dite_eq_right hf]

private theorem diskRestrictionEdgeExtension_apply
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip)) (d : D) :
    diskRestrictionEdgeExtension M S hflip c (edgeClass M d) =
      if hd : d ∈ S then
        c (edgeClass (inducedCombinatorialMap M S hflip) ⟨d, hd⟩) else 0 := by
  classical
  rfl

private theorem diskRestrictionEdgeExtension_cycle
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip))
    (hc : vertexBoundary (inducedCombinatorialMap M S hflip) c = 0) :
    vertexBoundary M (diskRestrictionEdgeExtension M S hflip c) = 0 := by
  classical
  let N := inducedCombinatorialMap M S hflip
  ext v
  change (∑ d : D, if vertexClass M d = v then
    diskRestrictionEdgeExtension M S hflip c (edgeClass M d) else 0) = 0
  simp_rw [diskRestrictionEdgeExtension_apply]
  have hsum : (∑ d : D, if vertexClass M d = v then
      (if hd : d ∈ S then c (edgeClass N ⟨d, hd⟩) else 0) else 0) =
      ∑ d : S, if vertexClass M d.1 = v then c (edgeClass N d) else 0 := by
    calc
      _ = ∑ d : D, if hd : d ∈ S then
          (if vertexClass M d = v then c (edgeClass N ⟨d, hd⟩) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : d ∈ S <;> by_cases hv : vertexClass M d = v <;> simp [hd, hv]
      _ = _ := by
        simpa only [Finset.univ_eq_attach] using
          (Finset.sum_attach_eq_sum_dite S (fun d : S =>
            if vertexClass M d.1 = v then c (edgeClass N d) else 0)).symm
  rw [hsum]
  by_cases hv : ∃ x : S, vertexClass M x.1 = v
  · obtain ⟨x, hx⟩ := hv
    have heq (d : S) : vertexClass M d.1 = v ↔
        vertexClass N d = vertexClass N x := by
      rw [← hx]
      constructor
      · intro h
        apply Quotient.sound
        exact (inducedCombinatorialMap_rot_sameCycle_iff M S hflip d x).mpr
          (Quotient.exact h)
      · intro h
        apply Quotient.sound
        exact (inducedCombinatorialMap_rot_sameCycle_iff M S hflip d x).mp
          (Quotient.exact h)
    simp_rw [heq]
    exact congrFun hc (vertexClass N x)
  · apply Finset.sum_eq_zero
    intro d _
    exact ite_eq_right (fun hd => hv ⟨d, hd⟩)

private theorem diskRestrictionFaceCoeff_corner
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (A : FaceSpace M) (d : D) :
    A (faceClass M d) = A (faceClass M (M.edgeInv (M.rot d))) := by
  apply congrArg A
  apply Quotient.sound
  change M.faceSucc.SameCycle d (M.edgeInv (M.rot d))
  have h : M.faceSucc.SameCycle (M.edgeInv (M.rot d))
      (M.faceSucc (M.edgeInv (M.rot d))) :=
    Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
  simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h.symm

private theorem diskRestrictionFaceCoeff_rot_eq
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S) (A : FaceSpace M)
    (hzero : ∀ d, d ∉ S → A (faceClass M d) = A (faceClass M (M.edgeInv d)))
    (z : {d : D // d ∈ S}) :
    A (faceClass M z.1) =
      A (faceClass M (M.edgeInv ((inducedCombinatorialMap M S hflip).rot z).1)) := by
  let k := cyclicFirstReturnTime M.rot S (finitePermutationReturn M.rot S) z
  have hk := cyclicFirstReturnTime_spec M.rot S (finitePermutationReturn M.rot S) z
  have hskip : ∀ j : ℕ, j < k →
      A (faceClass M ((M.rot ^ j) z.1)) = A (faceClass M z.1) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hdel : (M.rot ^ (j + 1)) z.1 ∉ S := hk.2.2 (j + 1) (by omega) hj
      calc
        _ = A (faceClass M (M.edgeInv ((M.rot ^ (j + 1)) z.1))) := hzero _ hdel
        _ = A (faceClass M ((M.rot ^ j) z.1)) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact (diskRestrictionFaceCoeff_corner M A _).symm
        _ = A (faceClass M z.1) := ih (by omega)
  have hreturn : ((inducedCombinatorialMap M S hflip).rot z).1 =
      (M.rot ^ k) z.1 :=
    (firstReturn_spec M.rot S (finitePermutationReturn M.rot S) z).1
  have hlast : k - 1 + 1 = k := by
    have := hk.1
    omega
  calc
    _ = A (faceClass M ((M.rot ^ (k - 1)) z.1)) := (hskip _ (by omega)).symm
    _ = A (faceClass M (M.edgeInv (M.rot ((M.rot ^ (k - 1)) z.1)))) := by
      exact diskRestrictionFaceCoeff_corner M A _
    _ = _ := by
      have hp : M.rot ((M.rot ^ (k - 1)) z.1) = (M.rot ^ k) z.1 := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', hlast]
      rw [hreturn, hp]

private theorem diskRestrictionFaceCoeff_faceSucc_eq
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S) (A : FaceSpace M)
    (hzero : ∀ d, d ∉ S → A (faceClass M d) = A (faceClass M (M.edgeInv d)))
    (z : {d : D // d ∈ S}) :
    A (faceClass M z.1) =
      A (faceClass M ((inducedCombinatorialMap M S hflip).faceSucc z).1) := by
  let N := inducedCombinatorialMap M S hflip
  have hrot := diskRestrictionFaceCoeff_rot_eq M S hflip A hzero (N.faceSucc z)
  have hval : M.edgeInv (N.rot (N.faceSucc z)).1 = z.1 := by
    simp [N, CombinatorialMap.faceSucc, inducedCombinatorialMap, M.edgeInv_invol]
  rw [hval] at hrot
  exact hrot.symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result.
Restricting a planar map to a nonempty, involution-closed dart set gives a
planar map whenever the induced first-return map is connected -/
theorem inducedCombinatorialMap_isPlanar_of_planar_connected
    {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (hM : M.IsPlanar) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hN : (inducedCombinatorialMap M S hflip).IsConnected)
    (hS : S.Nonempty) :
    (inducedCombinatorialMap M S hflip).IsPlanar := by
  classical
  let N := inducedCombinatorialMap M S hflip
  obtain ⟨d₀, hd₀⟩ := hS
  have hrange : LinearMap.range (faceBoundary N) = cycleSpace N := by
    apply le_antisymm
    · exact faceBoundary_range_le_cycleSpace N
    · intro c hc
      have hc0 : vertexBoundary N c = 0 := LinearMap.mem_ker.mp hc
      let cext := diskRestrictionEdgeExtension M S hflip c
      have hcext : vertexBoundary M cext = 0 :=
        diskRestrictionEdgeExtension_cycle M S hflip c hc0
      obtain ⟨A, hA⟩ := planar_cycle_eq_faceBoundary M hM cext hcext
      have hzero : ∀ d, d ∉ S →
          A (faceClass M d) = A (faceClass M (M.edgeInv d)) := by
        intro d hd
        have hz := congrFun hA (edgeClass M d)
        rw [faceBoundary_apply] at hz
        change A (faceClass M d) + A (faceClass M (M.edgeInv d)) =
          diskRestrictionEdgeExtension M S hflip c (edgeClass M d) at hz
        rw [diskRestrictionEdgeExtension_apply] at hz
        have hz' : A (faceClass M d) + A (faceClass M (M.edgeInv d)) = 0 := by
          simpa [hd] using hz
        calc
          A (faceClass M d) =
              A (faceClass M d) +
                (A (faceClass M (M.edgeInv d)) +
                  A (faceClass M (M.edgeInv d))) := by
            rw [CharTwo.add_self_eq_zero, add_zero]
          _ = A (faceClass M (M.edgeInv d)) := by
            rw [← add_assoc, hz', zero_add]
      let T : FaceSpace N := fun q =>
        Quotient.lift (fun x : {d : D // d ∈ S} => A (faceClass M x.1)) (by
          intro x y hxy
          obtain ⟨j, hj⟩ := hxy.exists_nat_pow_eq
          have hpow (j : ℕ) :
              A (faceClass M ((N.faceSucc ^ j) x).1) = A (faceClass M x.1) := by
            induction j with
            | zero => simp
            | succ j ih =>
              rw [pow_succ', Equiv.Perm.mul_apply]
              exact (diskRestrictionFaceCoeff_faceSucc_eq M S hflip A hzero
                ((N.faceSucc ^ j) x)).symm.trans ih
          have hxy' := hpow j
          rw [hj] at hxy'
          exact hxy'.symm) q
      have hT : faceBoundary N T = c := by
        ext q
        refine Quotient.inductionOn q ?_
        intro x
        have hAx := congrFun hA (edgeClass M x.1)
        rw [faceBoundary_apply] at hAx
        change A (faceClass M x.1) + A (faceClass M (M.edgeInv x.1)) =
          diskRestrictionEdgeExtension M S hflip c (edgeClass M x.1) at hAx
        rw [diskRestrictionEdgeExtension_apply] at hAx
        have hAx' : A (faceClass M x.1) +
            A (faceClass M (M.edgeInv x.1)) = c (edgeClass N x) := by
          simpa [x.2] using hAx
        change T (faceClass N x) + T (faceClass N (N.edgeInv x)) =
          c (edgeClass N x)
        have hval : (N.edgeInv x).1 = M.edgeInv x.1 := by
          simp [N, inducedCombinatorialMap]
        simp only [T, faceClass, Quotient.lift_mk]
        rw [hval]
        exact hAx'
      exact LinearMap.mem_range.mpr ⟨T, hT⟩
  exact ⟨hN, (@eulerChar_eq_two_iff_range_faceBoundary_eq_cycleSpace _ _ _ N
    ⟨⟨d₀, hd₀⟩⟩ hN).2 hrange⟩

/-- A missing-root framed ball inherits planarity from its ambient map whenever
toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem inducedFramedBallOfMissingRoot_isPlanar
    {D : Type} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (outer : {d : D // d ∈ S})
    (houter : ∀ d (hd : d ∈ S),
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer d →
        CombinatorialMap.IsOuter
          (inducedCombinatorialMap M.toCombinatorialMap S hflip)
          outer ⟨d, hd⟩)
    (root : {d : D // d ∈ S}) (hroot : M.missing root.1)
    (hM : M.toCombinatorialMap.IsPlanar)
    (hconnected :
      (inducedCombinatorialMap M.toCombinatorialMap S hflip).IsConnected) :
    (inducedFramedBallOfMissingRoot
      M S hflip outer houter root hroot).map.toCombinatorialMap.IsPlanar := by
  change (inducedCombinatorialMap M.toCombinatorialMap S hflip).IsPlanar
  exact inducedCombinatorialMap_isPlanar_of_planar_connected
    M.toCombinatorialMap hM S hflip hconnected ⟨root.1, root.2⟩

/-- The positive-radius disk stage ball has a planar underlying map
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem kmswDiskStageFramedBall_isPlanar {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    (kmswDiskStageFramedBall c k r hr).map.toCombinatorialMap.IsPlanar := by
  classical
  let u := finiteCodeExtend (n := n + 1) c.val
  let d := kmswDiskRootDart c k
  let s := kmswStage u n
  let S := kmswStageBallDarts (fun _ _ => True) s r
    (stageEndpoint s (edgeFlip _ d))
  let hf := fun e he => (kmswStageBallDarts_edgeFlip
    (fun _ _ => True) s r (stageEndpoint s (edgeFlip _ d)) e).mp he
  let root : S := ⟨d, (kmswDiskRootDart_ball_mem c k r hr).1⟩
  have hconnected := kmswStageBallCombinatorialMap_rooted_isConnected
    u n r d hr
  have hplanar := inducedCombinatorialMap_isPlanar_of_planar_connected
    (kmswStageDirectedMap u n).toCombinatorialMap (kmswMap_isPlanar u n)
    S hf hconnected ⟨d, root.2⟩
  change (kmswDiskStageFramedBall c k r hr).map.toCombinatorialMap.IsPlanar
  unfold kmswDiskStageFramedBall
  dsimp only [u, d, s, S, hf]
  exact hplanar


/-- Framed balls whose underlying combinatorial maps are planar and connected
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
@[expose] def PlanarConnectedFramedBall :=
  {B : FramedBall // B.map.toCombinatorialMap.IsPlanar ∧
    B.map.toCombinatorialMap.IsConnected}

/-- Isomorphism equivalence on planar connected framed balls
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
@[expose] def PlanarConnectedFramedBall.setoid :
    Setoid PlanarConnectedFramedBall where
  r M N := Nonempty (FramedBallIso M.1 N.1)
  iseqv := by
    constructor
    · intro M
      exact ⟨FramedBallIso.refl M.1⟩
    · intro M N h
      rcases h with ⟨I⟩
      exact ⟨FramedBallIso.symm I⟩
    · intro M N P hMN hNP
      rcases hMN with ⟨I⟩
      rcases hNP with ⟨J⟩
      exact ⟨FramedBallIso.trans I J⟩

/-- Isomorphism classes of planar connected framed balls
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
@[expose] def PlanarConnectedFramedBallClass :=
  Quotient PlanarConnectedFramedBall.setoid

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result.
Restrict a planar connected framed ball to a nonempty involution-closed dart
set, retaining a missing root dart and a marked outer face -/
@[expose] noncomputable def framedBallRestrict
    (B : PlanarConnectedFramedBall) (S : Finset B.1.D)
    (hflip : ∀ d, d ∈ S → B.1.map.edgeInv d ∈ S)
    (outer : {d : B.1.D // d ∈ S})
    (houter : ∀ d (hd : d ∈ S),
      CombinatorialMap.IsOuter B.1.map.toCombinatorialMap B.1.map.outer d →
        CombinatorialMap.IsOuter
          (inducedCombinatorialMap B.1.map.toCombinatorialMap S hflip)
          outer ⟨d, hd⟩)
    (root : {d : B.1.D // d ∈ S}) (hroot : B.1.map.missing root.1)
    (hconnected :
      (inducedCombinatorialMap B.1.map.toCombinatorialMap S hflip).IsConnected) :
    PlanarConnectedFramedBall := by
  let R := inducedFramedBallOfMissingRoot B.1.map S hflip outer houter root hroot
  have hS : S.Nonempty := ⟨root.1, root.2⟩
  have hplanar := inducedCombinatorialMap_isPlanar_of_planar_connected
    B.1.map.toCombinatorialMap B.2.1 S hflip hconnected hS
  exact ⟨R, hplanar, hconnected⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result.
The restricted framed ball retains its carrier, first-return rotation, outer
mark, ordered root incidences, missing tags, and orientations -/
theorem framedBallRestrict_data_spec
    (B : PlanarConnectedFramedBall) (S : Finset B.1.D)
    (hflip : ∀ d, d ∈ S → B.1.map.edgeInv d ∈ S)
    (outer : {d : B.1.D // d ∈ S})
    (houter : ∀ d (hd : d ∈ S),
      CombinatorialMap.IsOuter B.1.map.toCombinatorialMap B.1.map.outer d →
        CombinatorialMap.IsOuter
          (inducedCombinatorialMap B.1.map.toCombinatorialMap S hflip)
          outer ⟨d, hd⟩)
    (root : {d : B.1.D // d ∈ S}) (hroot : B.1.map.missing root.1)
    (hconnected :
      (inducedCombinatorialMap B.1.map.toCombinatorialMap S hflip).IsConnected) :
    let R := framedBallRestrict B S hflip outer houter root hroot hconnected
    R.1.D = {d : B.1.D // d ∈ S} ∧
      R.1.map.rot = cyclicFirstReturn B.1.map.toCombinatorialMap.rot S
        (finitePermutationReturn B.1.map.toCombinatorialMap.rot S) ∧
      R.1.map.outer = outer ∧
      R.1.rootDart = ⟨B.1.map.edgeInv root.1, hflip root.1 root.2⟩ ∧
      R.1.frameEdgeDart = R.1.rootDart ∧ R.1.frameOtherDart = some root ∧
      R.1.map.edgeInv R.1.rootDart = root ∧
      (∀ x : R.1.D, R.1.map.missing x ↔ B.1.map.missing x.1) ∧
      (∀ x : R.1.D, R.1.map.tail x ↔ B.1.map.tail x.1) := by
  dsimp only [framedBallRestrict]
  exact inducedFramedBallOfMissingRoot_data_spec B.1.map S hflip outer houter root hroot

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result.
The radius-`r'` disk stage ball is isomorphic to the restriction of the radius-`r` ball
to its radius-`r'` darts, rooted at the same missing root dart and with the outer face -/
@[expose] noncomputable def kmswDiskStageFramedBall_restrict_iso {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r r' : ℕ)
    (hr' : 0 < r') (hrr : r' ≤ r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let d := kmswDiskRootDart c k
    let Sbig := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r
      (stageEndpoint (kmswStage u n) (edgeFlip _ d))
    let Ssmall := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r'
      (stageEndpoint (kmswStage u n) (edgeFlip _ d))
    let hr : 0 < r := lt_of_lt_of_le hr' hrr
    let B : PlanarConnectedFramedBall :=
      ⟨kmswDiskStageFramedBall c k r hr, kmswDiskStageFramedBall_isPlanar c k r hr,
        kmswDiskStageFramedBall_isConnected c k r hr⟩
    let S : Finset B.1.D := firstReturnSubset Sbig Ssmall
    let hflip : ∀ x, x ∈ S → B.1.map.edgeInv x ∈ S :=
      inducedCombinatorialMap_nested_edgeInv_closed
        (kmswStageDirectedMap u n).toCombinatorialMap Sbig Ssmall
        (fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
          (kmswStage u n) r (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he)
        (fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
          (kmswStage u n) r' (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he)
    let outer : {x : B.1.D // x ∈ S} :=
      ⟨⟨d, (kmswDiskRootDart_ball_mem c k r hr).1⟩, by
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (kmswDiskRootDart_ball_mem c k r' hr').1⟩⟩
    let hconn : (inducedCombinatorialMap B.1.map.toCombinatorialMap S hflip).IsConnected := by
      exact kmswDiskStageBall_nested_isConnected c k r r' hr' hrr
    let houter : ∀ e (he : e ∈ S),
        CombinatorialMap.IsOuter B.1.map.toCombinatorialMap B.1.map.outer e →
          CombinatorialMap.IsOuter
            (inducedCombinatorialMap B.1.map.toCombinatorialMap S hflip) outer ⟨e, he⟩ :=
      fun e he ho => inducedCombinatorialMap_face_sameCycle_of_connected_planar
        B.1.map.toCombinatorialMap B.2.1 S hflip hconn outer ⟨e, he⟩ ho
    FramedBallIso (kmswDiskStageFramedBall c k r' hr')
      (framedBallRestrict B S hflip outer houter outer
        (kmswDiskRootDart_missing c k) hconn).1 := by
  intro u d Sbig Ssmall hr B S hflip outer hconn houter
  have hfBig := fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
    (kmswStage u n) r (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he
  have hfSmall := fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
    (kmswStage u n) r' (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he
  have hTS : ∀ e, e ∈ Ssmall → e ∈ Sbig :=
    fun e he => kmswStageBallDarts_inner_subset (fun _ _ => True) u n r r' _ hrr he
  change FramedBallIso (kmswDiskStageFramedBall c k r' hr')
    (inducedFramedBallOfMissingRoot B.1.map S hflip outer houter outer
      (kmswDiskRootDart_missing c k))
  have hrot := inducedCombinatorialMap_nested_rot_comm
    (kmswStageDirectedMap u n).toCombinatorialMap Sbig Ssmall hfBig hfSmall hTS
  have hedge := inducedCombinatorialMap_nested_edgeInv_comm
    (kmswStageDirectedMap u n).toCombinatorialMap Sbig Ssmall hfBig hfSmall hTS
  have hface := inducedCombinatorialMap_nested_faceSucc_comm
    (kmswStageDirectedMap u n).toCombinatorialMap Sbig Ssmall hfBig hfSmall hTS
  set E := inducedCombinatorialMap_nestedDartEquiv Sbig Ssmall hTS with hEdef
  have hrot' : ∀ y, E.symm ((kmswDiskStageFramedBall c k r' hr').map.rot y) =
      (inducedFramedBallOfMissingRoot B.1.map S hflip outer houter outer
        (kmswDiskRootDart_missing c k)).map.rot (E.symm y) := by
    intro y
    have key := hrot (E.symm y)
    have e1 : E (E.symm y) = y := E.apply_symm_apply y
    rw [e1] at key
    exact (E.symm_apply_eq).2 key.symm
  have hedge' : ∀ y, E.symm ((kmswDiskStageFramedBall c k r' hr').map.edgeInv y) =
      (inducedFramedBallOfMissingRoot B.1.map S hflip outer houter outer
        (kmswDiskRootDart_missing c k)).map.edgeInv (E.symm y) := by
    intro y
    have key := hedge (E.symm y)
    have e1 : E (E.symm y) = y := E.apply_symm_apply y
    rw [e1] at key
    exact (E.symm_apply_eq).2 key.symm
  let hmap : DirectedMapWithMissingIso (kmswDiskStageFramedBall c k r' hr').map
      (inducedFramedBallOfMissingRoot B.1.map S hflip outer houter outer
        (kmswDiskRootDart_missing c k)).map :=
    { toEquiv := E.symm
      rot_comm := hrot'
      edgeInv_comm := hedge'
      missing_iff := fun _ => Iff.rfl
      tail_iff := fun _ => Iff.rfl
      outer_iff := fun y => by
        have h := sameCycle_iff_of_intertwine _ _ E
          (fun x => hface x) outer (E.symm y)
        have e1 : E (E.symm y) = y := E.apply_symm_apply y
        rw [e1] at h
        exact h }
  have hroot : hmap.toEquiv (kmswDiskStageFramedBall c k r' hr').rootDart =
      (inducedFramedBallOfMissingRoot B.1.map S hflip outer houter outer
        (kmswDiskRootDart_missing c k)).rootDart :=
    hedge' ⟨d, (kmswDiskRootDart_ball_mem c k r' hr').1⟩
  refine ⟨hmap, ?_, hroot, ?_⟩
  · rw [hroot]
  · right
    exact ⟨outer, outer, rfl, rfl, Equiv.Perm.SameCycle.rfl⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result.
The radius-`r'` disk stage ball class is the class of the restriction of the radius-`r` -/
theorem diskStageBSBallClass_restrict {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r r' : ℕ)
    (hr' : 0 < r') (hrr : r' ≤ r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let d := kmswDiskRootDart c k
    let Sbig := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r
      (stageEndpoint (kmswStage u n) (edgeFlip _ d))
    let Ssmall := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r'
      (stageEndpoint (kmswStage u n) (edgeFlip _ d))
    let hr : 0 < r := lt_of_lt_of_le hr' hrr
    let B : PlanarConnectedFramedBall :=
      ⟨kmswDiskStageFramedBall c k r hr, kmswDiskStageFramedBall_isPlanar c k r hr,
        kmswDiskStageFramedBall_isConnected c k r hr⟩
    let S : Finset B.1.D := firstReturnSubset Sbig Ssmall
    let hflip : ∀ x, x ∈ S → B.1.map.edgeInv x ∈ S :=
      inducedCombinatorialMap_nested_edgeInv_closed
        (kmswStageDirectedMap u n).toCombinatorialMap Sbig Ssmall
        (fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
          (kmswStage u n) r (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he)
        (fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
          (kmswStage u n) r' (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he)
    let outer : {x : B.1.D // x ∈ S} :=
      ⟨⟨d, (kmswDiskRootDart_ball_mem c k r hr).1⟩, by
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (kmswDiskRootDart_ball_mem c k r' hr').1⟩⟩
    let hconn : (inducedCombinatorialMap B.1.map.toCombinatorialMap S hflip).IsConnected := by
      exact kmswDiskStageBall_nested_isConnected c k r r' hr' hrr
    let houter : ∀ e (he : e ∈ S),
        CombinatorialMap.IsOuter B.1.map.toCombinatorialMap B.1.map.outer e →
          CombinatorialMap.IsOuter
            (inducedCombinatorialMap B.1.map.toCombinatorialMap S hflip) outer ⟨e, he⟩ :=
      fun e he ho => inducedCombinatorialMap_face_sameCycle_of_connected_planar
        B.1.map.toCombinatorialMap B.2.1 S hflip hconn outer ⟨e, he⟩ ho
    diskStageBSBallClass r' hr' (c, k) =
      Quotient.mk FramedBall.setoid
        (framedBallRestrict B S hflip outer houter outer
          (kmswDiskRootDart_missing c k) hconn).1 :=
  Quotient.sound ⟨kmswDiskStageFramedBall_restrict_iso c k r r' hr' hrr⟩

end DirectedDistances.PaperProofs.Section5
