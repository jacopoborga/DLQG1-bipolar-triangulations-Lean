module

public import DirectedDistances.KMSW.MonotoneLayoutDrawing

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap



theorem nextEdge_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage w n).UR = e :: es) :
    (kmswStage w (n + 1)).nextEdge = (kmswStage w n).nextEdge := by
  simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hc, hUR]



theorem nextVertex_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage w n).UR = e :: es) :
    (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex := by
  simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hc, hUR]




theorem freshEdges_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage w n).UR = e :: es) :
    freshEdges w n = ∅ := by
  simp [freshEdges, nextEdge_activation w n hc e es hUR]



theorem layoutPos_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage w n).UR = e :: es) (v : ℕ) :
    layoutPos w (n + 1) v = layoutPos w n v := by
  have hgrow : ¬ (kmswStage w (n + 1)).nextVertex =
      (kmswStage w n).nextVertex + 1 := by
    rw [nextVertex_activation w n hc e es hUR]
    omega
  have hr : kmswStageRank w (n + 1) v = kmswStageRank w n v := by
    simp only [kmswStageRank]
    by_cases hv : v = (kmswStage w n).nextVertex
    · simp [hv, hc, hUR]
    · simp [hv]
  have hh : layoutHeight w (n + 1) v = layoutHeight w n v := by
    simp only [layoutHeight]
    split_ifs with h
    · exact False.elim (hgrow h.2)
    · rfl
  apply Complex.ext
  · change (↑(kmswStageRank w (n + 1) v) : ℝ) = ↑(kmswStageRank w n v)
    exact_mod_cast hr
  · exact hh



theorem layoutArc_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage w n).UR = e :: es) (i : ℕ) :
    layoutArc w (n + 1) i = layoutArc w n i := by
  simp [layoutArc, freshEdges_activation w n hc e es hUR]



theorem kmswCodeStep_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2) :
    kmswCodeStep (w n) = .down := by
  simp [kmswCodeStep, hc]




theorem stageRot_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage w n).UR = e :: es) :
    StageRotation.resize (nextEdge_activation w n hc e es hUR)
      (stageRot w (n + 1)) = stageRot w n := by
  rw [stageRot_succ]
  exact StageRotation.step_activation (kmswStage w n)
    (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n)
    (w n) (kmswCodeStep_activation w n hc) e es hUR




theorem stageVertex_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage w n).UR = e :: es)
    (d : StageDart (kmswStage w n).nextEdge) :
    (stageVertex w (n + 1)
      (Fin.cast (nextEdge_activation w n hc e es hUR).symm d.1, d.2)).val =
      (stageVertex w n d).val := by
  have hE := nextEdge_activation w n hc e es hUR
  cases d with
  | mk i b =>
    cases b with
    | false =>
      change (kmswStage w (n + 1)).west (Fin.cast hE.symm i).val =
        (kmswStage w n).west i.val
      rw [Fin.val_cast]
      simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hc, hUR]
    | true =>
      change (kmswStage w (n + 1)).east (Fin.cast hE.symm i).val =
        (kmswStage w n).east i.val
      rw [Fin.val_cast]
      simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hc, hUR]




theorem layoutDart_activation (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ) (hUR : (kmswStage w n).UR = e :: es)
    (d : StageDart (kmswStage w n).nextEdge) :
    layoutDart w (n + 1)
      (Fin.cast (nextEdge_activation w n hc e es hUR).symm d.1, d.2) =
      layoutDart w n d := by
  have hE := nextEdge_activation w n hc e es hUR
  cases d with
  | mk i b =>
    cases b with
    | false =>
      simp only [layoutDart, Bool.false_eq_true, ↓reduceIte]
      change layoutArc w (n + 1) (Fin.cast hE.symm i).val = layoutArc w n i.val
      rw [Fin.val_cast]
      exact layoutArc_activation w n hc e es hUR i.val
    | true =>
      simp only [layoutDart, ↓reduceIte]
      change (layoutArc w (n + 1) (Fin.cast hE.symm i).val).reverse =
        (layoutArc w n i.val).reverse
      rw [Fin.val_cast]
      exact congrArg (fun p : Polyline => p.reverse)
        (layoutArc_activation w n hc e es hUR i.val)

/-- Counterclockwise successor is preserved by an injective transport of the star.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem ccwSuccessor_of_injective {D D' : Type*} (c : D' → D)
    (hc : Function.Injective c) {S' : Set D'} {S : Set D}
    (hS : S' = c ⁻¹' S) (hsurj : S ⊆ Set.range c)
    (f' : D' → ℂ) (f : D → ℂ) (hf : ∀ x, f' x = f (c x))
    (d e : D') (h : CcwSuccessor S f (c d) (c e)) :
    CcwSuccessor S' f' d e := by
  have hfinite : S'.Finite := by
    rw [hS]
    exact h.1.preimage (by
      intro x hx y hy hxy
      exact hc hxy)
  have himage : c '' S' = S := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hS] using hy
    · intro hx
      rcases hsurj hx with ⟨y, rfl⟩
      refine ⟨y, ?_, rfl⟩
      rw [hS]
      exact Set.mem_preimage.mpr hx
  have hd : d ∈ S' := by
    rw [hS]
    exact h.2.1
  have he : e ∈ S' := by
    rw [hS]
    exact h.2.2.1
  rcases h.2.2.2 with hsingleton | hnext
  · rcases hsingleton with ⟨hee, hstar⟩
    have hS' : S' = {d} := by
      ext x
      constructor
      · intro hx
        have hximage : c x ∈ c '' S' := ⟨x, hx, rfl⟩
        rw [himage, hstar] at hximage
        exact hc hximage
      · intro hxd
        subst x
        rw [hS]
        exact Set.mem_preimage.mpr h.2.1
    exact ⟨hfinite, hd, he, Or.inl ⟨hc hee, hS'⟩⟩
  · refine ⟨hfinite, hd, he, Or.inr ?_⟩
    refine ⟨?_, fun x hx hxd => ?_⟩
    · intro hxed
      exact hnext.1 (congrArg c hxed)
    · have hxS : c x ∈ S := by
        have hx' : x ∈ c ⁻¹' S := by simpa [hS] using hx
        exact hx'
      have hxc : c x ≠ c d := by
        intro hxc
        exact hxd (hc hxc)
      simpa only [hf] using hnext.2 (c x) hxS hxc

private theorem resize_apply_cast {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) (d : StageDart l) :
    StageRotation.resize h σ d =
      (Fin.cast h (σ (Fin.cast h.symm d.1, d.2)).1,
        (σ (Fin.cast h.symm d.1, d.2)).2) := by
  subst h
  rfl

/-- ACT leaves the good layout structure unchanged under dart-carrier transport.
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem layoutGood_succ_act (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2)
    (e : ℕ) (es : List ℕ)
    (hUR : (kmswStage w n).UR = e :: es) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) : LayoutGood w (n + 1) := by
  let hE := nextEdge_activation w n hc e es hUR
  let hV := nextVertex_activation w n hc e es hUR
  let c : StageDart (kmswStage w (n + 1)).nextEdge →
      StageDart (kmswStage w n).nextEdge :=
    fun d => (Fin.cast hE d.1, d.2)
  let c' : StageDart (kmswStage w n).nextEdge →
      StageDart (kmswStage w (n + 1)).nextEdge :=
    fun d => (Fin.cast hE.symm d.1, d.2)
  have hcc (d : StageDart (kmswStage w n).nextEdge) : c (c' d) = d := by
    cases d with
    | mk i b => cases b <;> simp [c, c']
  have hcc' (d : StageDart (kmswStage w (n + 1)).nextEdge) : c' (c d) = d := by
    cases d with
    | mk i b => cases b <;> simp [c, c']
  have hc_inj : Function.Injective c := by
    intro d e hde
    apply Prod.ext
    · apply Fin.ext
      have hfst := congrArg Prod.fst hde
      simpa [c] using congrArg Fin.val hfst
    · simpa [c] using congrArg Prod.snd hde
  have hflip (d : StageDart (kmswStage w (n + 1)).nextEdge) :
      c (edgeFlip _ d) = edgeFlip _ (c d) := by
    cases d with
    | mk i b => cases b <;> rfl
  have hLayout (d : StageDart (kmswStage w (n + 1)).nextEdge) :
      layoutDart w (n + 1) d = layoutDart w n (c d) := by
    rw [← hcc' d]
    exact layoutDart_activation w n hc e es hUR (c d)
  have hVertexVal (d : StageDart (kmswStage w (n + 1)).nextEdge) :
      (stageVertex w (n + 1) d).val = (stageVertex w n (c d)).val := by
    simpa [c, c'] using stageVertex_activation w n hc e es hUR (c d)
  have hRot (d : StageDart (kmswStage w (n + 1)).nextEdge) :
      stageRot w n (c d) = c (stageRot w (n + 1) d) := by
    have h := congrArg (fun σ : Equiv.Perm (StageDart (kmswStage w n).nextEdge) =>
      σ (c d)) (stageRot_activation w n hc e es hUR)
    rw [resize_apply_cast] at h
    simpa [c, c'] using h.symm
  let H := layoutGood_of_invariant G
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d f hfd hfflip
    have hcd : c f ≠ c d := fun h => hfd (hc_inj h)
    have hcflip : c f ≠ edgeFlip _ (c d) := by
      intro hf
      apply hfflip
      apply hc_inj
      calc
        c f = edgeFlip _ (c d) := hf
        _ = c (edgeFlip _ d) := (hflip d).symm
    rw [hLayout d, hLayout f]
    exact H.interior_disjoint (c d) (c f) hcd hcflip
  · intro d v
    rw [hLayout d, layoutPos_activation w n hc e es hUR v.val]
    simpa [Fin.val_cast] using H.interior_avoids_vertices (c d) (Fin.cast hV v)
  · intro d f hvertex harg
    have hvertex' : stageVertex w n (c d) = stageVertex w n (c f) := by
      apply Fin.ext
      have hval := congrArg Fin.val hvertex
      rw [hVertexVal d, hVertexVal f] at hval
      exact hval
    rw [hLayout d, hLayout f] at harg
    have hde := H.initial_arg_injective (c d) (c f) hvertex' harg
    exact hc_inj hde
  · intro d
    let S' : Set (StageDart (kmswStage w (n + 1)).nextEdge) :=
      {f | stageVertex w (n + 1) f = stageVertex w (n + 1) d}
    let S : Set (StageDart (kmswStage w n).nextEdge) :=
      {f | stageVertex w n f = stageVertex w n (c d)}
    have hS : S' = c ⁻¹' S := by
      apply Set.ext
      intro f
      change stageVertex w (n + 1) f = stageVertex w (n + 1) d ↔
        stageVertex w n (c f) = stageVertex w n (c d)
      constructor
      · intro h
        apply Fin.ext
        have hv := congrArg Fin.val h
        rw [hVertexVal f, hVertexVal d] at hv
        exact hv
      · intro h
        apply Fin.ext
        have hv := congrArg Fin.val h
        rw [hVertexVal f, hVertexVal d]
        exact hv
    have hsurj : S ⊆ Set.range c := by
      intro x hx
      exact ⟨c' x, hcc x⟩
    have hdir (x : StageDart (kmswStage w (n + 1)).nextEdge) :
        (layoutDart w (n + 1) x).initialDirection =
          (layoutDart w n (c x)).initialDirection := by
      rw [hLayout]
    have hOld := H.rotation_agreement (c d)
    rw [hRot d] at hOld
    exact ccwSuccessor_of_injective c hc_inj hS hsurj
      (fun x => (layoutDart w (n + 1) x).initialDirection)
      (fun x => (layoutDart w n x).initialDirection) hdir d
      (stageRot w (n + 1) d) hOld

end DirectedDistances.KMSW
