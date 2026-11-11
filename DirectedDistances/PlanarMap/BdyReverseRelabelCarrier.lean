/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BdyReverseRelabel

/-! # Relabelling the restricted boundary carrier

Restricted helper toward `lem-bdy-reverse`
declarations are helpers only and are not counted as the paper result. -/

public section
namespace DirectedDistances.PlanarMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

def relabelOrbitEquiv (σ : Equiv.Perm D) (f : Equiv.Perm D) :
    Quotient (Equiv.Perm.SameCycle.setoid f) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (relabelPerm σ f)) := by
  classical
  apply Quotient.congr σ
  intro x y
  change Equiv.Perm.SameCycle f x y ↔
    Equiv.Perm.SameCycle (relabelPerm σ f) (σ x) (σ y)
  constructor
  · intro h
    exact h.conj
  · intro h
    simpa using
      (Equiv.Perm.sameCycle_conj (g := σ) (f := f)
        (x := σ x) (y := σ y)).mp h

theorem combinatorialMap_relabel_numVertices (σ : Equiv.Perm D)
    (M : CombinatorialMap D) :
    (CombinatorialMap.relabel σ M).numVertices = M.numVertices := by
  classical
  unfold CombinatorialMap.numVertices
  exact (Fintype.card_congr (relabelOrbitEquiv σ M.rot)).symm

theorem combinatorialMap_relabel_numEdges (σ : Equiv.Perm D)
    (M : CombinatorialMap D) :
    (CombinatorialMap.relabel σ M).numEdges = M.numEdges := by
  classical
  unfold CombinatorialMap.numEdges
  exact (Fintype.card_congr (relabelOrbitEquiv σ M.edgeInv)).symm

theorem combinatorialMap_relabel_numFaces (σ : Equiv.Perm D)
    (M : CombinatorialMap D) :
    (CombinatorialMap.relabel σ M).numFaces = M.numFaces := by
  classical
  unfold CombinatorialMap.numFaces
  change Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid
      (CombinatorialMap.relabel σ M).faceSucc)) =
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid M.faceSucc))
  rw [CombinatorialMap.relabel_faceSucc]
  exact (Fintype.card_congr (relabelOrbitEquiv σ M.faceSucc)).symm

theorem combinatorialMap_relabel_faceSucc_apply (σ : Equiv.Perm D)
    (M : CombinatorialMap D) (d : D) :
    (CombinatorialMap.relabel σ M).faceSucc d =
      σ (M.faceSucc (σ.symm d)) := by
  simp [CombinatorialMap.relabel_faceSucc, relabelPerm_apply]

omit [Fintype D] [DecidableEq D] in
theorem relabelPerm_inv (σ f : Equiv.Perm D) :
    (relabelPerm σ f)⁻¹ = relabelPerm σ f⁻¹ := by
  simp [relabelPerm, mul_assoc]

omit [Fintype D] [DecidableEq D] in
theorem relabelPerm_symm_apply (σ f : Equiv.Perm D) (d : D) :
    (relabelPerm σ f).symm d = σ (f.symm (σ.symm d)) := by
  change (relabelPerm σ f)⁻¹ d = σ (f⁻¹ (σ⁻¹ d))
  rw [relabelPerm_inv]
  exact relabelPerm_apply σ f⁻¹ d

theorem combinatorialMap_relabel_connected (σ : Equiv.Perm D)
    (M : CombinatorialMap D) (hM : M.IsConnected) :
    (CombinatorialMap.relabel σ M).IsConnected := by
  intro d e
  let R := fun x y : D =>
    y = M.rot x ∨ y = M.rot.symm x ∨ y = M.edgeInv x ∨ y = M.edgeInv.symm x
  let R' := fun x y : D =>
    y = (CombinatorialMap.relabel σ M).rot x ∨
      y = (CombinatorialMap.relabel σ M).rot.symm x ∨
      y = (CombinatorialMap.relabel σ M).edgeInv x ∨
      y = (CombinatorialMap.relabel σ M).edgeInv.symm x
  have hstep : ∀ x y, R (σ.symm x) (σ.symm y) ↔ R' x y := by
    intro x y
    dsimp only [R, R']
    constructor
    · rintro (h | h | h | h)
      · left
        calc
          y = σ (σ.symm y) := by simp
          _ = σ (M.rot (σ.symm x)) := congrArg σ h
          _ = (relabelPerm σ M.rot) x := by simp [relabelPerm_apply]
      · right; left
        calc
          y = σ (σ.symm y) := by simp
          _ = σ (M.rot.symm (σ.symm x)) := congrArg σ h
          _ = (relabelPerm σ M.rot).symm x := relabelPerm_symm_apply σ M.rot x
      · right; right; left
        calc
          y = σ (σ.symm y) := by simp
          _ = σ (M.edgeInv (σ.symm x)) := congrArg σ h
          _ = (relabelPerm σ M.edgeInv) x := by simp [relabelPerm_apply]
      · right; right; right
        calc
          y = σ (σ.symm y) := by simp
          _ = σ (M.edgeInv.symm (σ.symm x)) := congrArg σ h
          _ = (relabelPerm σ M.edgeInv).symm x := relabelPerm_symm_apply σ M.edgeInv x
    · rintro (h | h | h | h)
      · left
        apply σ.injective
        calc
          σ (σ.symm y) = y := by simp
          _ = σ (M.rot (σ.symm x)) := by simpa [relabelPerm_apply] using h
      · right; left
        apply σ.injective
        calc
          σ (σ.symm y) = y := by simp
          _ = σ (M.rot.symm (σ.symm x)) := by
            calc
              y = (relabelPerm σ M.rot).symm x := h
              _ = σ (M.rot.symm (σ.symm x)) := relabelPerm_symm_apply σ M.rot x
      · right; right; left
        apply σ.injective
        calc
          σ (σ.symm y) = y := by simp
          _ = σ (M.edgeInv (σ.symm x)) := by simpa [relabelPerm_apply] using h
      · right; right; right
        apply σ.injective
        calc
          σ (σ.symm y) = y := by simp
          _ = σ (M.edgeInv.symm (σ.symm x)) := by
            calc
              y = (relabelPerm σ M.edgeInv).symm x := h
              _ = σ (M.edgeInv.symm (σ.symm x)) := relabelPerm_symm_apply σ M.edgeInv x
  have hstep' : ∀ x y, R x y ↔ R' (σ x) (σ y) := by
    intro x y
    simpa using hstep (σ x) (σ y)
  have hreach := hM (σ.symm d) (σ.symm e)
  have hmap : ∀ {x y}, Relation.ReflTransGen R x y →
      Relation.ReflTransGen R' (σ x) (σ y) := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hlast ih =>
        exact Relation.ReflTransGen.tail ih ((hstep' _ _).mp hlast)
  have hreach' := hmap hreach
  simpa [R', CombinatorialMap.relabel_rot, CombinatorialMap.relabel_edgeInv,
    relabelPerm_apply] using hreach'

theorem combinatorialMap_relabel_isPlanar (σ : Equiv.Perm D)
    (M : CombinatorialMap D) (hM : M.IsPlanar) :
    (CombinatorialMap.relabel σ M).IsPlanar := by
  refine ⟨combinatorialMap_relabel_connected σ M hM.1, ?_⟩
  simpa only [CombinatorialMap.eulerChar,
    combinatorialMap_relabel_numVertices,
    combinatorialMap_relabel_numEdges,
    combinatorialMap_relabel_numFaces] using hM.2

theorem directedStep_relabel_iff (σ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) (u v : MapVertex M) :
    (DirectedMapWithMissing.relabel σ M).directedStep
      (DirectedMapWithMissing.relabelVertexEquiv σ M u)
      (DirectedMapWithMissing.relabelVertexEquiv σ M v) ↔
      M.directedStep u v := by
  constructor
  · rintro ⟨d, hmiss, htail, htailV, hheadV⟩
    let d₀ := σ.symm d
    refine ⟨d₀, ?_, ?_, ?_, ?_⟩
    · simpa [d₀] using hmiss
    · simpa [d₀] using htail
    · have htailV' :
          DirectedMapWithMissing.relabelVertexEquiv σ M (dartTailVertex M d₀) =
            DirectedMapWithMissing.relabelVertexEquiv σ M u := by
        have hd : d = σ d₀ := by simp [d₀]
        rw [DirectedMapWithMissing.relabelVertexEquiv_dartTailVertex σ M d₀]
        rw [← hd]
        exact htailV
      exact (DirectedMapWithMissing.relabelVertexEquiv σ M).injective htailV'
    · have hheadV' :
          DirectedMapWithMissing.relabelVertexEquiv σ M (dartHeadVertex M d₀) =
            DirectedMapWithMissing.relabelVertexEquiv σ M v := by
        have hd : d = σ d₀ := by simp [d₀]
        rw [DirectedMapWithMissing.relabelVertexEquiv_dartHeadVertex σ M d₀]
        rw [← hd]
        exact hheadV
      exact (DirectedMapWithMissing.relabelVertexEquiv σ M).injective hheadV'
  · rintro ⟨d, hmiss, htail, htailV, hheadV⟩
    refine ⟨σ d, ?_, ?_, ?_, ?_⟩
    · simpa using hmiss
    · simpa using htail
    · calc
        dartTailVertex (DirectedMapWithMissing.relabel σ M) (σ d) =
            DirectedMapWithMissing.relabelVertexEquiv σ M (dartTailVertex M d) :=
          (DirectedMapWithMissing.relabelVertexEquiv_dartTailVertex σ M d).symm
        _ = DirectedMapWithMissing.relabelVertexEquiv σ M u :=
          congrArg (DirectedMapWithMissing.relabelVertexEquiv σ M) htailV
    · calc
        dartHeadVertex (DirectedMapWithMissing.relabel σ M) (σ d) =
            DirectedMapWithMissing.relabelVertexEquiv σ M (dartHeadVertex M d) :=
          (DirectedMapWithMissing.relabelVertexEquiv_dartHeadVertex σ M d).symm
        _ = DirectedMapWithMissing.relabelVertexEquiv σ M v :=
          congrArg (DirectedMapWithMissing.relabelVertexEquiv σ M) hheadV

theorem directedMap_relabel_isAcyclic (σ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic) :
    (DirectedMapWithMissing.relabel σ M).IsAcyclic := by
  intro v hcycle
  let e := DirectedMapWithMissing.relabelVertexEquiv σ M
  have hcycle' : Relation.TransGen M.directedStep (e.symm v) (e.symm v) := by
    have hmap := hcycle.lift e.symm (fun x y hxy => by
      have hxy' := (directedStep_relabel_iff σ M (e.symm x) (e.symm y)).mp
        (by simpa [e] using hxy)
      simpa [e] using hxy')
    simpa [e] using hmap
  exact hM (e.symm v) hcycle'

theorem relabel_isOuter_iff (σ : Equiv.Perm D) (M : DirectedMapWithMissing D)
    (d : D) :
    (DirectedMapWithMissing.relabel σ M).IsOuter d ↔ M.IsOuter (σ.symm d) := by
  change CombinatorialMap.IsOuter
      (CombinatorialMap.relabel σ M.toCombinatorialMap) (σ M.outer) d ↔
    CombinatorialMap.IsOuter M.toCombinatorialMap M.outer (σ.symm d)
  simpa only [Equiv.apply_symm_apply] using
    CombinatorialMap.relabel_isOuter_iff σ M.toCombinatorialMap M.outer (σ.symm d)

theorem relabel_ulDarts (σ : Equiv.Perm D) (M : DirectedMapWithMissing D)
    (d : D) :
    d ∈ (DirectedMapWithMissing.relabel σ M).ulDarts ↔
      σ.symm d ∈ M.ulDarts := by
  simp only [DirectedMapWithMissing.ulDarts, Set.mem_ofPred_eq,
    DirectedMapWithMissing.relabel_missing, DirectedMapWithMissing.relabel_tail]
  constructor
  · rintro ⟨hm, ht, ho⟩
    exact ⟨by simpa using hm, by simpa using ht,
      (relabel_isOuter_iff σ M d).mp ho⟩
  · rintro ⟨hm, ht, ho⟩
    exact ⟨by simpa using hm, by simpa using ht,
      (relabel_isOuter_iff σ M d).mpr ho⟩

theorem relabel_lrDarts (σ : Equiv.Perm D) (M : DirectedMapWithMissing D)
    (d : D) :
    d ∈ (DirectedMapWithMissing.relabel σ M).lrDarts ↔
      σ.symm d ∈ M.lrDarts := by
  simp only [DirectedMapWithMissing.lrDarts, Set.mem_ofPred_eq,
    DirectedMapWithMissing.relabel_missing, DirectedMapWithMissing.relabel_tail]
  constructor
  · rintro ⟨hm, ht, ho⟩
    exact ⟨by simpa using hm, by simpa using ht,
      (relabel_isOuter_iff σ M d).mp ho⟩
  · rintro ⟨hm, ht, ho⟩
    exact ⟨by simpa using hm, by simpa using ht,
      (relabel_isOuter_iff σ M d).mpr ho⟩

omit [Fintype D] in
theorem formPerm_map_relabel (σ : Equiv.Perm D) : ∀ xs : List D,
    (xs.map σ).formPerm = relabelPerm σ xs.formPerm
  | [] => by simp [relabelPerm]
  | [a] => by simp [relabelPerm]
  | a :: b :: xs => by
      have hswap : σ * Equiv.swap a b * σ⁻¹ = Equiv.swap (σ a) (σ b) := by
        ext x
        by_cases hxa : x = σ a
        · subst x
          simp
        · by_cases hxb : x = σ b
          · subst x
            simp
          · have hsa : σ.symm x ≠ a := by
              intro h
              apply hxa
              calc
                x = σ (σ.symm x) := by simp
                _ = σ a := congrArg σ h
            have hsb : σ.symm x ≠ b := by
              intro h
              apply hxb
              calc
                x = σ (σ.symm x) := by simp
                _ = σ b := congrArg σ h
            simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hxa, hxb, hsa, hsb]
      have hrec : (σ b :: xs.map σ).formPerm =
          relabelPerm σ (b :: xs).formPerm := by
        simpa only [List.map_cons] using formPerm_map_relabel σ (b :: xs)
      simp only [List.map_cons, List.formPerm_cons_cons]
      rw [hrec, ← hswap]
      simp [relabelPerm, mul_assoc]

theorem isOuterCycle_relabel (σ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) (W : NonemptyWord D)
    (hW : IsOuterCycle M W) :
    IsOuterCycle (DirectedMapWithMissing.relabel σ M)
      (NonemptyWord.relabel σ W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    have hd₀' : M.IsOuter (σ.symm (σ d₀)) := by
      rw [Equiv.symm_apply_apply]
      exact hW.1 d₀ hd₀
    exact (relabel_isOuter_iff σ M (σ d₀)).2 hd₀'
  · intro d hd
    have hd₀ : M.IsOuter (σ.symm d) :=
      (relabel_isOuter_iff σ M d).1 hd
    exact List.mem_map.mpr ⟨σ.symm d, hW.2.1 _ hd₀, by simp⟩
  · intro d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    calc
      (DirectedMapWithMissing.relabel σ M).toCombinatorialMap.faceSucc (σ d₀) =
          σ (M.toCombinatorialMap.faceSucc d₀) := by
            simpa using combinatorialMap_relabel_faceSucc_apply σ M.toCombinatorialMap (σ d₀)
      _ = σ (W.letters.formPerm d₀) := congrArg σ (hW.2.2 d₀ hd₀)
      _ = (W.letters.map σ).formPerm (σ d₀) := by
            rw [formPerm_map_relabel]
            simp [relabelPerm_apply]

theorem fourArcsWitness_relabel (σ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) (W : NonemptyWord D)
    (ul ur lr ll : List D)
    (h : FourArcsWitness M W ul ur lr ll) :
    FourArcsWitness (DirectedMapWithMissing.relabel σ M)
      (NonemptyWord.relabel σ W) (ul.map σ) (ur.map σ) (lr.map σ) (ll.map σ) := by
  refine ⟨isOuterCycle_relabel σ M W h.1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [NonemptyWord.relabel_letters, List.map_append] using h.2.1.map σ
  · intro d
    simp only [List.mem_map]
    rw [relabel_ulDarts]
    constructor
    · rintro ⟨d₀, hd₀, rfl⟩
      have hd₀' : σ.symm (σ d₀) ∈ M.ulDarts := by
        rw [Equiv.symm_apply_apply]
        exact (h.2.2.1 d₀).mp hd₀
      exact hd₀'
    · intro hd
      exact ⟨σ.symm d, (h.2.2.1 (σ.symm d)).mpr hd, by simp⟩
  · intro d
    simp only [List.mem_map]
    rw [relabel_lrDarts]
    constructor
    · rintro ⟨d₀, hd₀, rfl⟩
      have hd₀' : σ.symm (σ d₀) ∈ M.lrDarts := by
        rw [Equiv.symm_apply_apply]
        exact (h.2.2.2.1 d₀).mp hd₀
      exact hd₀'
    · intro hd
      exact ⟨σ.symm d, (h.2.2.2.1 (σ.symm d)).mpr hd, by simp⟩
  · intro d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    simpa using h.2.2.2.2.1 d₀ hd₀
  · intro d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    simpa using h.2.2.2.2.2 d₀ hd₀

/-- Relabel a restricted bipolar triangulation with boundary. This transports
the full combinatorial, directed, path, and outer-face carrier
helper only and not counted. -/
@[expose] noncomputable def BipolarTriangulationWithBoundary.relabel
    {ℓ r : ℕ} (σ : Equiv.Perm D)
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    BipolarTriangulationWithBoundary D ℓ r where
  map := DirectedMapWithMissing.relabel σ B.map
  noMissingDarts := by
    intro d
    simpa using B.noMissingDarts (σ.symm d)
  planar := combinatorialMap_relabel_isPlanar σ B.map.toCombinatorialMap B.planar
  innerFacesDegreeThree := by
    intro d hd
    have hd' : ¬ B.map.IsOuter (σ.symm d) := by
      intro ho
      apply hd
      exact (relabel_isOuter_iff σ B.map d).2 ho
    rcases B.innerFacesDegreeThree (σ.symm d) hd' with ⟨h3, h1, h2⟩
    have hface (x : D) : (DirectedMapWithMissing.relabel σ B.map).toCombinatorialMap.faceSucc x =
        σ (B.map.toCombinatorialMap.faceSucc (σ.symm x)) :=
      combinatorialMap_relabel_faceSucc_apply σ B.map.toCombinatorialMap x
    refine ⟨?_, ?_, ?_⟩
    · calc
        (DirectedMapWithMissing.relabel σ B.map).toCombinatorialMap.faceSucc
          ((DirectedMapWithMissing.relabel σ B.map).toCombinatorialMap.faceSucc
            ((DirectedMapWithMissing.relabel σ B.map).toCombinatorialMap.faceSucc d)) =
            σ (B.map.toCombinatorialMap.faceSucc
              (B.map.toCombinatorialMap.faceSucc
                (B.map.toCombinatorialMap.faceSucc (σ.symm d)))) := by
                  simp only [hface, Equiv.symm_apply_apply]
        _ = d := by simpa only [Equiv.apply_symm_apply] using congrArg σ h3
    · intro heq
      apply h1
      apply σ.injective
      calc
        σ (B.map.toCombinatorialMap.faceSucc (σ.symm d)) = d := by
          calc
            σ (B.map.toCombinatorialMap.faceSucc (σ.symm d)) =
                (DirectedMapWithMissing.relabel σ B.map).toCombinatorialMap.faceSucc d :=
              (hface d).symm
            _ = d := heq
        _ = σ (σ.symm d) := by simp
    · intro heq
      apply h2
      apply σ.injective
      calc
        σ (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc (σ.symm d))) = d := by
          calc
            σ (B.map.toCombinatorialMap.faceSucc
              (B.map.toCombinatorialMap.faceSucc (σ.symm d))) =
                (DirectedMapWithMissing.relabel σ B.map).toCombinatorialMap.faceSucc
                  ((DirectedMapWithMissing.relabel σ B.map).toCombinatorialMap.faceSucc d) := by
                    simp only [hface, Equiv.symm_apply_apply]
            _ = d := heq
        _ = σ (σ.symm d) := by simp
  acyclic := directedMap_relabel_isAcyclic σ B.map B.acyclic
  source := DirectedMapWithMissing.relabelVertexEquiv σ B.map B.source
  sink := DirectedMapWithMissing.relabelVertexEquiv σ B.map B.sink
  isSource := by
    rintro ⟨v, hv⟩
    let e := DirectedMapWithMissing.relabelVertexEquiv σ B.map
    apply B.isSource
    refine ⟨e.symm v, ?_⟩
    have hv' : (DirectedMapWithMissing.relabel σ B.map).directedStep
        (e (e.symm v)) (e B.source) := by
      simpa [e] using hv
    exact (directedStep_relabel_iff σ B.map (e.symm v) B.source).mp hv'
  source_unique := by
    intro v hv
    let e := DirectedMapWithMissing.relabelVertexEquiv σ B.map
    have hv' : ¬ ∃ u, B.map.directedStep u (e.symm v) := by
      rintro ⟨u, hu⟩
      apply hv
      refine ⟨e u, ?_⟩
      simpa [e] using (directedStep_relabel_iff σ B.map u (e.symm v)).2 hu
    exact (Equiv.apply_symm_apply e v).symm.trans
      (congrArg e (B.source_unique _ hv'))
  isSink := by
    rintro ⟨v, hv⟩
    let e := DirectedMapWithMissing.relabelVertexEquiv σ B.map
    apply B.isSink
    refine ⟨e.symm v, ?_⟩
    have hv' : (DirectedMapWithMissing.relabel σ B.map).directedStep
        (e B.sink) (e (e.symm v)) := by
      simpa [e] using hv
    exact (directedStep_relabel_iff σ B.map B.sink (e.symm v)).mp hv'
  sink_unique := by
    intro v hv
    let e := DirectedMapWithMissing.relabelVertexEquiv σ B.map
    have hv' : ¬ ∃ w, B.map.directedStep (e.symm v) w := by
      rintro ⟨w, hw⟩
      apply hv
      refine ⟨e w, ?_⟩
      simpa [e] using (directedStep_relabel_iff σ B.map (e.symm v) w).2 hw
    exact (Equiv.apply_symm_apply e v).symm.trans
      (congrArg e (B.sink_unique _ hv'))
  left_length_pos := B.left_length_pos
  right_length_pos := B.right_length_pos
  outerWord := NonemptyWord.relabel σ B.outerWord
  leftPath := SimpleDirectedDartPath.relabel σ B.leftPath
  rightPath := SimpleDirectedDartPath.relabel σ B.rightPath
  paths_internally_vertex_disjoint := by
    intro v hvL hvR
    rw [SimpleDirectedDartPath.relabel_vertices] at hvL hvR
    obtain ⟨vL, hvL0, hvvL⟩ := List.mem_map.mp hvL
    obtain ⟨vR, hvR0, hvvR⟩ := List.mem_map.mp hvR
    have hvEq' : vL = vR :=
      (DirectedMapWithMissing.relabelVertexEquiv σ B.map).injective
        (hvvL.trans hvvR.symm)
    subst vR
    rcases B.paths_internally_vertex_disjoint vL hvL0 hvR0 with h | h
    · exact Or.inl (hvvL.symm.trans (congrArg _ h))
    · exact Or.inr (hvvL.symm.trans (congrArg _ h))
  paths_edge_disjoint := by
    intro d hd e he hcycle
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
    rcases List.mem_map.mp he with ⟨e₀, he₀, rfl⟩
    apply B.paths_edge_disjoint d₀ hd₀ e₀ he₀
    have hcycle' := (Equiv.Perm.sameCycle_conj (g := σ)
      (f := B.map.toCombinatorialMap.edgeInv)
      (x := σ d₀) (y := σ e₀)).mp hcycle
    simpa using hcycle'
  outerSplit := by
    have hlist :
        (B.rightPath.darts.map σ).reverse.map
            (CombinatorialMap.relabel σ B.map.toCombinatorialMap).edgeInv =
          (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).map σ := by
      simp [List.map_reverse, List.map_map, Function.comp_def,
        CombinatorialMap.relabel_edgeInv, relabelPerm_apply]
    have hlist' :
        (B.rightPath.darts.map σ).reverse.map
            (DirectedMapWithMissing.relabel σ B.map).edgeInv =
          (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).map σ := by
      change (B.rightPath.darts.map σ).reverse.map
          (CombinatorialMap.relabel σ B.map.toCombinatorialMap).edgeInv = _
      exact hlist
    rw [SimpleDirectedDartPath.relabel_darts]
    rw [SimpleDirectedDartPath.relabel_darts]
    rw [hlist']
    exact fourArcsWitness_relabel σ B.map B.outerWord B.leftPath.darts []
      (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv) [] B.outerSplit

/-- The relabelled carrier has the same inner-edge count
helper only and not counted. -/
theorem BipolarTriangulationWithBoundary.relabel_innerEdgeCount
    {ℓ r : ℕ} (σ : Equiv.Perm D)
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    innerEdgeCount (B.relabel σ) = innerEdgeCount B := by
  simp [innerEdgeCount, BipolarTriangulationWithBoundary.relabel,
    combinatorialMap_relabel_numEdges]

/-- Relabelling preserves boundary-channeled membership
helper only and not counted. -/
theorem BipolarTriangulationWithBoundary.relabel_mem_boundaryVertices
    {ℓ r : ℕ} (σ : Equiv.Perm D)
    (B : BipolarTriangulationWithBoundary D ℓ r) (v : MapVertex B.map) :
    DirectedMapWithMissing.relabelVertexEquiv σ B.map v ∈
        (B.relabel σ).boundaryVertices ↔ v ∈ B.boundaryVertices := by
  change (DirectedMapWithMissing.relabelVertexEquiv σ B.map v ∈
      (SimpleDirectedDartPath.relabel σ B.leftPath).vertices ∨
    DirectedMapWithMissing.relabelVertexEquiv σ B.map v ∈
      (SimpleDirectedDartPath.relabel σ B.rightPath).vertices) ↔ _
  rw [SimpleDirectedDartPath.relabel_vertices, SimpleDirectedDartPath.relabel_vertices]
  constructor
  · rintro (hv | hv)
    · left
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp hv
      have : w = v := (DirectedMapWithMissing.relabelVertexEquiv σ B.map).injective heq
      simpa [this] using hw
    · right
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp hv
      have : w = v := (DirectedMapWithMissing.relabelVertexEquiv σ B.map).injective heq
      simpa [this] using hw
  · rintro (hv | hv)
    · exact Or.inl (List.mem_map.mpr ⟨v, hv, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem BipolarTriangulationWithBoundary.relabel_boundaryEdge_iff
    {ℓ r : ℕ} (σ : Equiv.Perm D)
    (B : BipolarTriangulationWithBoundary D ℓ r) (d : D) :
    (B.relabel σ).boundaryEdge (σ d) ↔ B.boundaryEdge d := by
  change (∃ a ∈ B.leftPath.darts.map σ ++ B.rightPath.darts.map σ,
      Equiv.Perm.SameCycle (relabelPerm σ B.map.toCombinatorialMap.edgeInv)
        (σ d) a) ↔
    (∃ a ∈ B.leftPath.darts ++ B.rightPath.darts,
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d a)
  constructor
  · rintro ⟨a, ha, hcycle⟩
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
      refine ⟨a₀, List.mem_append.mpr (Or.inl ha₀), ?_⟩
      have hc := (Equiv.Perm.sameCycle_conj (g := σ)
        (f := B.map.toCombinatorialMap.edgeInv) (x := σ d) (y := σ a₀)).mp hcycle
      simpa using hc
    · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
      refine ⟨a₀, List.mem_append.mpr (Or.inr ha₀), ?_⟩
      have hc := (Equiv.Perm.sameCycle_conj (g := σ)
        (f := B.map.toCombinatorialMap.edgeInv) (x := σ d) (y := σ a₀)).mp hcycle
      simpa using hc
  · rintro ⟨a, ha, hcycle⟩
    rcases List.mem_append.mp ha with ha | ha
    · refine ⟨σ a, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)), ?_⟩
      exact hcycle.conj
    · refine ⟨σ a, List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩)), ?_⟩
      exact hcycle.conj

theorem BipolarTriangulationWithBoundary.relabel_InMbc_iff
    {ℓ r : ℕ} (σ : Equiv.Perm D)
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    InMbc ℓ r (B.relabel σ) ↔ InMbc ℓ r B := by
  change (B.relabel σ).IsBoundaryChanneled ↔ B.IsBoundaryChanneled
  constructor
  · intro hbc d hm ht hv hne
    let e := DirectedMapWithMissing.relabelVertexEquiv σ B.map
    have hm' : ¬ (B.relabel σ).map.missing (σ d) := by
      simpa [BipolarTriangulationWithBoundary.relabel] using hm
    have ht' : (B.relabel σ).map.tail (σ d) := by
      simpa [BipolarTriangulationWithBoundary.relabel] using ht
    have hhead : dartHeadVertex (B.relabel σ).map (σ d) =
        e (dartHeadVertex B.map d) := by
      change dartHeadVertex (DirectedMapWithMissing.relabel σ B.map) (σ d) = _
      exact (DirectedMapWithMissing.relabelVertexEquiv_dartHeadVertex σ B.map d).symm
    have hv' : dartHeadVertex (B.relabel σ).map (σ d) ∈
        (B.relabel σ).boundaryVertices := by
      have hv'' :=
        (BipolarTriangulationWithBoundary.relabel_mem_boundaryVertices σ B _).2 hv
      rw [← hhead] at hv''
      exact hv''
    have hne' : dartHeadVertex (B.relabel σ).map (σ d) ≠ (B.relabel σ).sink := by
      intro hh
      apply hne
      apply e.injective
      have hh' : dartHeadVertex (B.relabel σ).map (σ d) = e B.sink := by
        simpa [BipolarTriangulationWithBoundary.relabel] using hh
      exact hhead.symm.trans hh'
    exact (BipolarTriangulationWithBoundary.relabel_boundaryEdge_iff σ B d).mp
      (hbc (σ d) hm' ht' hv' hne')
  · intro hbc d' hm ht hv hne
    let d := σ.symm d'
    let e := DirectedMapWithMissing.relabelVertexEquiv σ B.map
    have hm' : ¬ B.map.missing d := by
      simpa [d, BipolarTriangulationWithBoundary.relabel] using hm
    have ht' : B.map.tail d := by
      simpa [d, BipolarTriangulationWithBoundary.relabel] using ht
    have hv' : dartHeadVertex B.map d ∈ B.boundaryVertices := by
      have hd : d' = σ d := by simp [d]
      have hvEq : dartHeadVertex (B.relabel σ).map d' =
          e (dartHeadVertex B.map d) := by
        rw [hd]
        change dartHeadVertex (DirectedMapWithMissing.relabel σ B.map) (σ d) = _
        exact (DirectedMapWithMissing.relabelVertexEquiv_dartHeadVertex σ B.map d).symm
      have hvNew := hv
      rw [hvEq] at hvNew
      exact (BipolarTriangulationWithBoundary.relabel_mem_boundaryVertices σ B _).1 hvNew
    have hne' : dartHeadVertex B.map d ≠ B.sink := by
      intro hh
      apply hne
      have hd : d' = σ d := by simp [d]
      have hvEq : dartHeadVertex (B.relabel σ).map d' =
          e (dartHeadVertex B.map d) := by
        rw [hd]
        change dartHeadVertex (DirectedMapWithMissing.relabel σ B.map) (σ d) = _
        exact (DirectedMapWithMissing.relabelVertexEquiv_dartHeadVertex σ B.map d).symm
      rw [hvEq]
      change e (dartHeadVertex B.map d) = e B.sink
      exact congrArg e hh
    have hedge := (BipolarTriangulationWithBoundary.relabel_boundaryEdge_iff σ B d).mpr
      (hbc d hm' ht' hv' hne')
    simpa [d] using hedge

/-- The selected right-prefix edge orbits transport by relabelling
helper only and not counted. -/
theorem rightPrefixFlipDarts_relabel {ℓ r : ℕ}
    (σ : Equiv.Perm D) (B : BipolarTriangulationWithBoundary D ℓ r)
    (k : ℕ) :
    rightPrefixFlipDarts (B.relabel σ) k =
      relabelDartSet σ (rightPrefixFlipDarts B k) := by
  rw [rightPrefixFlipDarts_eq_prefixFlipDartSet,
    rightPrefixFlipDarts_eq_prefixFlipDartSet]
  simp only [BipolarTriangulationWithBoundary.relabel,
    SimpleDirectedDartPath.relabel_darts,
    DirectedMapWithMissing.relabel_combinatorialMap]
  exact (relabel_prefixFlipDartSet σ B.map.toCombinatorialMap
    B.rightPath.darts k).symm

/-- Orientation reversal of a transported edge-orbit set commutes with -/
theorem flipOrientation_relabel {σ : Equiv.Perm D}
    (M : DirectedMapWithMissing D) (S S' : Set D)
    (hS : (∀ d, d ∈ S → M.toCombinatorialMap.edgeInv d ∈ S) ∧
      (∀ d, d ∈ S → ¬ M.missing d))
    (hS' : (∀ d, d ∈ S' →
        (DirectedMapWithMissing.relabel σ M).toCombinatorialMap.edgeInv d ∈
          S') ∧
      (∀ d, d ∈ S' →
        ¬ (DirectedMapWithMissing.relabel σ M).missing d))
    (hmem : ∀ d, d ∈ S' ↔ σ.symm d ∈ S) :
    flipOrientation (DirectedMapWithMissing.relabel σ M)
        S' hS' =
      DirectedMapWithMissing.relabel σ (flipOrientation M S hS) := by
  cases M with
  | mk cm missing missing_edgeInv tail tail_iff tail_missing outer missing_outer =>
      simp [flipOrientation, DirectedMapWithMissing.relabel,
        hmem, CombinatorialMap.relabel_edgeInv, relabelPerm_apply]
      funext d
      rw [hmem d]

/-- The right-prefix flipped map commutes with dart relabelling
helper only and not counted. -/
theorem flipRightPrefix_relabel {ℓ r : ℕ}
    (σ : Equiv.Perm D) (B : BipolarTriangulationWithBoundary D ℓ r)
    (k : ℕ) (hk : 1 ≤ k) (hkr : k < r) :
    flipRightPrefix (B.relabel σ) k hk hkr =
      DirectedMapWithMissing.relabel σ (flipRightPrefix B k hk hkr) := by
  have hset := rightPrefixFlipDarts_relabel σ B k
  have hmem : ∀ d, d ∈ rightPrefixFlipDarts (B.relabel σ) k ↔
      σ.symm d ∈ rightPrefixFlipDarts B k := by
    intro d
    rw [hset, relabelDartSet_mem]
  change flipOrientation (B.relabel σ).map
      (rightPrefixFlipDarts (B.relabel σ) k)
      (rightPrefixFlip_condition (B.relabel σ) k) =
    DirectedMapWithMissing.relabel σ
      (flipOrientation B.map (rightPrefixFlipDarts B k)
        (rightPrefixFlip_condition B k))
  exact flipOrientation_relabel B.map (rightPrefixFlipDarts B k)
    (rightPrefixFlipDarts (B.relabel σ) k)
    (rightPrefixFlip_condition B k) (rightPrefixFlip_condition (B.relabel σ) k)
    hmem

/-- The map field of right-prefix reversal commutes with dart relabelling
helper only and not counted. -/
theorem rightPrefixReversal_relabel_map {ℓ r : ℕ}
    (σ : Equiv.Perm D) (B : BipolarTriangulationWithBoundary D ℓ r)
    (k : ℕ) (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (rightPrefixReversal (B.relabel σ) k hk hkr
      ((B.relabel_InMbc_iff σ).2 hbc)).map =
      DirectedMapWithMissing.relabel σ
        (rightPrefixReversal B k hk hkr hbc).map := by
  have hbc0 : BipolarTriangulationWithBoundary.InMbc ℓ r B := hbc
  have hbc' : BipolarTriangulationWithBoundary.InMbc ℓ r (B.relabel σ) :=
    (B.relabel_InMbc_iff σ).2 hbc0
  rw [rightPrefixReversal_map (B := B.relabel σ) k hk hkr hbc',
    rightPrefixReversal_map B k hk hkr hbc0]
  exact flipRightPrefix_relabel σ B k hk hkr

/-- Relabelling acts on the boundary-channeled carrier class
helper only and not counted. -/
@[expose] noncomputable def relabelBoundaryMbcClass {ℓ r : ℕ} (σ : Equiv.Perm D) :
    BoundaryMbcClass D ℓ r → BoundaryMbcClass D ℓ r := fun B =>
  ⟨B.val.relabel σ, (B.val.relabel_InMbc_iff σ).2 B.property⟩

/-- The reversed left-boundary dart list commutes with dart relabelling
helper only and not counted. -/
theorem rightPrefixReversal_relabel_leftPath_darts {ℓ r : ℕ}
    (σ : Equiv.Perm D) (B : BipolarTriangulationWithBoundary D ℓ r)
    (k : ℕ) (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (rightPrefixReversal (B.relabel σ) k hk hkr
      ((B.relabel_InMbc_iff σ).2 hbc)).leftPath.darts =
      ((rightPrefixReversal B k hk hkr hbc).leftPath.darts).map σ := by
  have hbc0 : BipolarTriangulationWithBoundary.InMbc ℓ r B := hbc
  have hbc' : BipolarTriangulationWithBoundary.InMbc ℓ r (B.relabel σ) :=
    (B.relabel_InMbc_iff σ).2 hbc0
  rw [rightPrefixReversal_leftPath_darts (B := B.relabel σ) k hk hkr hbc',
    rightPrefixReversal_leftPath_darts B k hk hkr hbc0]
  simp only [BipolarTriangulationWithBoundary.relabel,
    SimpleDirectedDartPath.relabel_darts, DirectedMapWithMissing.relabel_combinatorialMap]
  exact relabel_rightPrefixLeftDarts σ B.map.toCombinatorialMap
    B.leftPath.darts B.rightPath.darts k

/-- The retained right-boundary dart list commutes with dart relabelling
helper only and not counted. -/
theorem rightPrefixReversal_relabel_rightPath_darts {ℓ r : ℕ}
    (σ : Equiv.Perm D) (B : BipolarTriangulationWithBoundary D ℓ r)
    (k : ℕ) (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (rightPrefixReversal (B.relabel σ) k hk hkr
      ((B.relabel_InMbc_iff σ).2 hbc)).rightPath.darts =
      ((rightPrefixReversal B k hk hkr hbc).rightPath.darts).map σ := by
  have hbc0 : BipolarTriangulationWithBoundary.InMbc ℓ r B := hbc
  have hbc' : BipolarTriangulationWithBoundary.InMbc ℓ r (B.relabel σ) :=
    (B.relabel_InMbc_iff σ).2 hbc0
  rw [rightPrefixReversal_rightPath_darts (B := B.relabel σ) k hk hkr hbc',
    rightPrefixReversal_rightPath_darts B k hk hkr hbc0]
  simp only [BipolarTriangulationWithBoundary.relabel,
    SimpleDirectedDartPath.relabel_darts]
  exact relabel_rightPrefixRightDarts σ B.rightPath.darts k

/-- Extensionality for the data fields of the relabelled carrier. Proof fields
are propositionally irrelevant (`lem-bdy-reverse`,
counted. -/
theorem BipolarTriangulationWithBoundary.hext_fields
    {ℓ r : ℕ} {B C : BipolarTriangulationWithBoundary D ℓ r}
    (hmap : B.map = C.map) (hsource : HEq B.source C.source)
    (hsink : HEq B.sink C.sink) (hword : B.outerWord = C.outerWord)
    (hleft : HEq B.leftPath C.leftPath) (hright : HEq B.rightPath C.rightPath) :
    B = C := by
  cases B with
  | mk bm bn bp bf ba bs bt bis bsu bit btu blp brp bw bl br bd be bo =>
    cases C with
    | mk cm cn cp cf ca cs ct cis csu cit ctu clp crp cw cl cr cd ce co =>
      dsimp at hmap hsource hsink hword hleft hright
      cases hmap
      cases hsource
      cases hsink
      cases hword
      cases hleft
      cases hright
      rfl

theorem relabelVertexEquiv_one_heq (M : DirectedMapWithMissing D)
    (v : MapVertex M) :
    HEq (DirectedMapWithMissing.relabelVertexEquiv 1 M v) v := by
  have hM := DirectedMapWithMissing.relabel_one M
  cases hM
  induction v using Quotient.inductionOn with
  | h d =>
      apply heq_of_eq
      change Quotient.congr (1 : Equiv.Perm D) _ (Quotient.mk _ d) =
        Quotient.mk _ ((1 : Equiv.Perm D) d)
      exact Quotient.congr_mk (1 : Equiv.Perm D) _ d

theorem relabelVertexEquiv_mul_heq (σ τ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) (v : MapVertex M) :
    HEq (DirectedMapWithMissing.relabelVertexEquiv (σ * τ) M v)
      (DirectedMapWithMissing.relabelVertexEquiv σ
        (DirectedMapWithMissing.relabel τ M)
        (DirectedMapWithMissing.relabelVertexEquiv τ M v)) := by
  have hM := DirectedMapWithMissing.relabel_mul σ τ M
  cases hM
  induction v using Quotient.inductionOn with
  | h d =>
      apply heq_of_eq
      change Quotient.congr (σ * τ) _ (Quotient.mk _ d) =
        Quotient.congr σ _ (Quotient.congr τ _ (Quotient.mk _ d))
      simp only [Quotient.congr_mk]
      rfl

end DirectedDistances.PlanarMap
