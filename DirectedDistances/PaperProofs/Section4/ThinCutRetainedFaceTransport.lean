module

public import DirectedDistances.PaperProofs.Section4.ThinCutMarkedRestrictionCompatibility
public import DirectedDistances.PaperProofs.Section4.ThinCutSideColoringTransport

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open DirectedDistances.PaperProofs.Section3
open scoped Classical

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An outer dart is on the left boundary or is the reverse of a right-boundary
dart. This is the outer-arc characterization used for both path-cut halves. -/
theorem isOuter_iff_mem_left_or_reverse_right_boundary
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    B.map.IsOuter d ↔
      d ∈ B.leftPath.darts ∨
        ∃ e ∈ B.rightPath.darts, d = B.map.toCombinatorialMap.edgeInv e := by
  rw [isOuter_iff_mem_outerArcs]
  constructor
  · rintro (hl | hr)
    · exact Or.inl ((mem_pathCutLeftOuterArc_iff B d).mp hl)
    · rw [mem_pathCutRightOuterArc_iff] at hr
      obtain ⟨e, he, hde⟩ := List.mem_map.mp hr
      exact Or.inr ⟨e, List.mem_reverse.mp he, hde.symm⟩
  · rintro (hl | ⟨e, he, hde⟩)
    · exact Or.inl ((mem_pathCutLeftOuterArc_iff B d).mpr hl)
    · apply Or.inr
      rw [mem_pathCutRightOuterArc_iff]
      apply List.mem_map.mpr
      exact ⟨e, List.mem_reverse.mpr he, hde.symm⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A selected outer dart of the left half is either on a surviving original
boundary index or on a surviving reversed seam index. Source: -/
theorem cutLRep_selected_outer_boundary_or_seam
    {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (s : ℕ) (v : MapVertex (cutLRep R hR).2.B.map)
    (hs : s + 1 ≤ ℓ)
    (hv : boundaryTarget (cutLRep R hR).2.B .left s = some v)
    (d : Fin (cutLRep R hR).2.dartCount)
    (hd : d ∈ selectedDarts (presentation (cutLRep R hR).2 .left v)) :
    ∃ c < m,
      (cutLRep R hR).2.B.map.IsOuter d ↔
        (∃ i, i < s ∧
          (boundaryDarts (cutLRep R hR).2.B .left)[i]? = some d) ∨
        (∃ i, i < c ∧
          ∃ e : selectedDarts (presentation (cutLRep R hR).2 .left v),
            (boundaryDarts (cutLRep R hR).2.B .right)[i]? = some e.1 ∧
              d = (cutLRep R hR).2.B.map.toCombinatorialMap.edgeInv e.1) := by
  obtain ⟨c, hc, hindices⟩ :=
    seam_selectedDart_initial_segment (cutLRep R hR).2 .left s v hs hv
  have hcm : c < m := by
    simpa only [oppositeSide, boundaryDarts,
      (cutLRep R hR).2.B.rightPath.darts_length] using hc
  refine ⟨c, hcm, ?_⟩
  constructor
  · intro ho
    rcases (isOuter_iff_mem_left_or_reverse_right_boundary
      (cutLRep R hR).2.B d).mp ho with hleft | ⟨e, he, hde⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hleft
      have hget : (boundaryDarts (cutLRep R hR).2.B .left)[i]? = some d := by
        change (cutLRep R hR).2.B.leftPath.darts[i]? = some d
        exact (List.getElem?_eq_getElem i.isLt).trans (congrArg some hi)
      have hindex := (boundary_selectedDart_index_iff (cutLRep R hR).2
        .left s i.val v d hv hget).mp hd
      exact Or.inl ⟨i.val, hindex, hget⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
      have hget : (boundaryDarts (cutLRep R hR).2.B .right)[i]? = some e := by
        change (cutLRep R hR).2.B.rightPath.darts[i]? = some e
        exact (List.getElem?_eq_getElem i.isLt).trans (congrArg some hi)
      have hsel : e ∈ selectedDarts (presentation (cutLRep R hR).2 .left v) := by
        change dartTailVertex (cutLRep R hR).2.B.map e ∈
            ancestors (presentation (cutLRep R hR).2 .left v) ∧
          dartHeadVertex (cutLRep R hR).2.B.map e ∈
            ancestors (presentation (cutLRep R hR).2 .left v)
        have hd' := hd
        change dartTailVertex (cutLRep R hR).2.B.map d ∈
            ancestors (presentation (cutLRep R hR).2 .left v) ∧
          dartHeadVertex (cutLRep R hR).2.B.map d ∈
            ancestors (presentation (cutLRep R hR).2 .left v) at hd'
        rw [hde] at hd'
        exact ⟨by simpa [dartTailVertex, dartHeadVertex,
          (cutLRep R hR).2.B.map.edgeInv_invol] using hd'.2,
          by simpa only [dartTailVertex, dartHeadVertex] using hd'.1⟩
      have hindex := (hindices i.val).mp ⟨⟨e, hsel⟩, hget⟩
      exact Or.inr ⟨i.val, hindex, ⟨⟨e, hsel⟩, hget, hde⟩⟩
  · rintro (hleft | ⟨i, hi, e, hget, hde⟩)
    · obtain ⟨i, hi, hget⟩ := hleft
      obtain ⟨hi', hval⟩ := List.getElem?_eq_some_iff.mp hget
      have hmem : d ∈ (boundaryDarts (cutLRep R hR).2.B .left) := by
        apply List.mem_iff_get.mpr
        exact ⟨⟨i, hi'⟩, hval⟩
      exact (isOuter_iff_mem_left_or_reverse_right_boundary
        (cutLRep R hR).2.B d).mpr (Or.inl hmem)
    · obtain ⟨hi', hval⟩ := List.getElem?_eq_some_iff.mp hget
      have hmem : e.1 ∈ (boundaryDarts (cutLRep R hR).2.B .right) := by
        apply List.mem_iff_get.mpr
        exact ⟨⟨i, hi'⟩, hval⟩
      exact (isOuter_iff_mem_left_or_reverse_right_boundary
        (cutLRep R hR).2.B d).mpr (Or.inr ⟨e.1, hmem, hde⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A selected outer dart of the right half is either on a surviving original
boundary index or on a surviving seam index. Source: -/
theorem cutRRep_selected_outer_boundary_or_seam
    {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (s : ℕ) (v : MapVertex (cutRRep R hR).2.B.map)
    (hs : s + 1 ≤ r)
    (hv : boundaryTarget (cutRRep R hR).2.B .right s = some v)
    (d : Fin (cutRRep R hR).2.dartCount)
    (hd : d ∈ selectedDarts (presentation (cutRRep R hR).2 .right v)) :
    ∃ c < m,
      (cutRRep R hR).2.B.map.IsOuter d ↔
        (∃ i, i < s ∧
          ∃ e : selectedDarts (presentation (cutRRep R hR).2 .right v),
            (boundaryDarts (cutRRep R hR).2.B .right)[i]? = some e.1 ∧
              d = (cutRRep R hR).2.B.map.toCombinatorialMap.edgeInv e.1) ∨
        (∃ i, i < c ∧
          (boundaryDarts (cutRRep R hR).2.B .left)[i]? = some d) := by
  obtain ⟨c, hc, hindices⟩ :=
    seam_selectedDart_initial_segment (cutRRep R hR).2 .right s v hs hv
  have hcm : c < m := by
    simpa only [oppositeSide, boundaryDarts,
      (cutRRep R hR).2.B.leftPath.darts_length] using hc
  refine ⟨c, hcm, ?_⟩
  constructor
  · intro ho
    rcases (isOuter_iff_mem_left_or_reverse_right_boundary
      (cutRRep R hR).2.B d).mp ho with hseam | ⟨e, he, hde⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hseam
      have hget : (boundaryDarts (cutRRep R hR).2.B .left)[i]? = some d := by
        exact (List.getElem?_eq_getElem i.isLt).trans (congrArg some hi)
      have hindex := (hindices i.val).mp ⟨⟨d, hd⟩, hget⟩
      exact Or.inr ⟨i.val, hindex, hget⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
      have hget : (boundaryDarts (cutRRep R hR).2.B .right)[i]? = some e := by
        exact (List.getElem?_eq_getElem i.isLt).trans (congrArg some hi)
      have hsel : e ∈ selectedDarts (presentation (cutRRep R hR).2 .right v) := by
        have hd' := hd
        change dartTailVertex (cutRRep R hR).2.B.map d ∈
            ancestors (presentation (cutRRep R hR).2 .right v) ∧
          dartHeadVertex (cutRRep R hR).2.B.map d ∈
            ancestors (presentation (cutRRep R hR).2 .right v) at hd'
        rw [hde] at hd'
        change dartTailVertex (cutRRep R hR).2.B.map e ∈
            ancestors (presentation (cutRRep R hR).2 .right v) ∧
          dartHeadVertex (cutRRep R hR).2.B.map e ∈
            ancestors (presentation (cutRRep R hR).2 .right v)
        exact ⟨by simpa [dartTailVertex, dartHeadVertex,
          (cutRRep R hR).2.B.map.edgeInv_invol] using hd'.2,
          by simpa only [dartTailVertex, dartHeadVertex] using hd'.1⟩
      have hindex := (boundary_selectedDart_index_iff (cutRRep R hR).2
        .right s i.val v e hv hget).mp hsel
      exact Or.inl ⟨i.val, hindex, ⟨⟨e, hsel⟩, hget, hde⟩⟩
  · rintro (⟨i, hi, e, hget, hde⟩ | hseam)
    · obtain ⟨hi', hval⟩ := List.getElem?_eq_some_iff.mp hget
      have hmem : e.1 ∈ (boundaryDarts (cutRRep R hR).2.B .right) := by
        apply List.mem_iff_get.mpr
        exact ⟨⟨i, hi'⟩, hval⟩
      exact (isOuter_iff_mem_left_or_reverse_right_boundary
        (cutRRep R hR).2.B d).mpr (Or.inr ⟨e.1, hmem, hde⟩)
    · obtain ⟨i, hi, hget⟩ := hseam
      obtain ⟨hi', hval⟩ := List.getElem?_eq_some_iff.mp hget
      have hmem : d ∈ (boundaryDarts (cutRRep R hR).2.B .left) := by
        apply List.mem_iff_get.mpr
        exact ⟨⟨i, hi'⟩, hval⟩
      exact (isOuter_iff_mem_left_or_reverse_right_boundary
        (cutRRep R hR).2.B d).mpr (Or.inl hmem)

private theorem directedIso_faceSucc_comm
    {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {N : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M N) (d : D) :
    I.toEquiv (M.toCombinatorialMap.faceSucc d) =
      N.toCombinatorialMap.faceSucc (I.toEquiv d) := by
  have hr (e : D) : I.toEquiv (M.rot.symm e) = N.rot.symm (I.toEquiv e) := by
    apply N.rot.injective
    calc
      N.rot (I.toEquiv (M.rot.symm e)) = I.toEquiv (M.rot (M.rot.symm e)) :=
        (I.rot_comm _).symm
      _ = I.toEquiv e := by simp
      _ = N.rot (N.rot.symm (I.toEquiv e)) := by simp
  change I.toEquiv (M.rot.symm (M.edgeInv d)) =
    N.rot.symm (N.edgeInv (I.toEquiv d))
  rw [hr, I.edgeInv_comm]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Left retained-face transport needs common-face orbit compatibility only for -/
theorem cutLRep_retainedFace_iff_of_image_eq_of_nonouter
    {x : XDP} {ℓ r n m ℓ' r' n' m' : ℕ} {α : Type*}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (σ : Equiv.Perm α) (F : Fin R.dartCount → α) (G : Fin S.dartCount → α)
    (hF : Function.Injective F) (hG : Function.Injective G)
    (himg : (F ∘ cutLRepDartMap R hR) ''
      selectedDarts (presentation (cutLRep R hR).2 .left v) =
        (G ∘ cutLRepDartMap S hS) ''
          selectedDarts (presentation (cutLRep S hS).2 .left v'))
    (d : Fin (cutLRep R hR).2.dartCount)
    (e : Fin (cutLRep S hS).2.dartCount)
    (hde : F (cutLRepDartMap R hR d) = G (cutLRepDartMap S hS e))
    (hout : (cutLRep R hR).2.B.map.IsOuter d ↔
      (cutLRep S hS).2.B.map.IsOuter e)
    (hF' : ¬ (cutLRep R hR).2.B.map.IsOuter d →
      ∀ z, Equiv.Perm.SameCycle σ (F (cutLRepDartMap R hR d)) z ↔
        ∃ e', Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
          (cutLRepDartMap R hR d) e' ∧ F e' = z)
    (hG' : ¬ (cutLRep S hS).2.B.map.IsOuter e →
      ∀ z, Equiv.Perm.SameCycle σ (G (cutLRepDartMap S hS e)) z ↔
        ∃ e', Equiv.Perm.SameCycle S.B.map.toCombinatorialMap.faceSucc
          (cutLRepDartMap S hS e) e' ∧ G e' = z) :
    retainedFace (presentation (cutLRep R hR).2 .left v) d ↔
      retainedFace (presentation (cutLRep S hS).2 .left v') e := by
  rw [cutLRep_retainedFace_iff_selected_image R hR v d,
    cutLRep_retainedFace_iff_selected_image S hS v' e]
  constructor
  · rintro ⟨hd, hcov⟩
    have he : ¬ (cutLRep S hS).2.B.map.IsOuter e := (not_congr hout).mp hd
    refine ⟨he, ?_⟩
    have hleft := (faceOrbit_subset_iff_common σ F hF (cutLRepDartMap R hR)
      R.B.map.toCombinatorialMap.faceSucc
      (selectedDarts (presentation (cutLRep R hR).2 .left v)) d (hF' hd)).mp hcov
    have hright : ∀ z, Equiv.Perm.SameCycle σ
        (G (cutLRepDartMap S hS e)) z →
        z ∈ (G ∘ cutLRepDartMap S hS) ''
          selectedDarts (presentation (cutLRep S hS).2 .left v') := by
      intro z hz
      have hz' : Equiv.Perm.SameCycle σ
          (F (cutLRepDartMap R hR d)) z := by rw [hde]; exact hz
      rw [← himg]
      exact hleft z hz'
    exact (faceOrbit_subset_iff_common σ G hG (cutLRepDartMap S hS)
      S.B.map.toCombinatorialMap.faceSucc
      (selectedDarts (presentation (cutLRep S hS).2 .left v')) e
      (hG' he)).mpr hright
  · rintro ⟨he, hcov⟩
    have hd : ¬ (cutLRep R hR).2.B.map.IsOuter d := (not_congr hout).mpr he
    refine ⟨hd, ?_⟩
    have hright := (faceOrbit_subset_iff_common σ G hG (cutLRepDartMap S hS)
      S.B.map.toCombinatorialMap.faceSucc
      (selectedDarts (presentation (cutLRep S hS).2 .left v')) e (hG' he)).mp hcov
    have hleft : ∀ z, Equiv.Perm.SameCycle σ
        (F (cutLRepDartMap R hR d)) z →
        z ∈ (F ∘ cutLRepDartMap R hR) ''
          selectedDarts (presentation (cutLRep R hR).2 .left v) := by
      intro z hz
      have hz' : Equiv.Perm.SameCycle σ
          (G (cutLRepDartMap S hS e)) z := by rw [← hde]; exact hz
      rw [himg]
      exact hright z hz'
    exact (faceOrbit_subset_iff_common σ F hF (cutLRepDartMap R hR)
      R.B.map.toCombinatorialMap.faceSucc
      (selectedDarts (presentation (cutLRep R hR).2 .left v)) d
      (hF' hd)).mpr hleft

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Right retained-face transport needs common-face orbit compatibility only for -/
theorem cutRRep_retainedFace_iff_of_image_eq_of_nonouter
    {x : XDP} {ℓ r n m ℓ' r' n' m' : ℕ} {α : Type*}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (σ : Equiv.Perm α) (F : Fin R.dartCount → α) (G : Fin S.dartCount → α)
    (hF : Function.Injective F) (hG : Function.Injective G)
    (himg : (F ∘ cutRRepDartMap R hR) ''
      selectedDarts (presentation (cutRRep R hR).2 .right v) =
        (G ∘ cutRRepDartMap S hS) ''
          selectedDarts (presentation (cutRRep S hS).2 .right v'))
    (d : Fin (cutRRep R hR).2.dartCount)
    (e : Fin (cutRRep S hS).2.dartCount)
    (hde : F (cutRRepDartMap R hR d) = G (cutRRepDartMap S hS e))
    (hout : (cutRRep R hR).2.B.map.IsOuter d ↔
      (cutRRep S hS).2.B.map.IsOuter e)
    (hF' : ¬ (cutRRep R hR).2.B.map.IsOuter d →
      ∀ z, Equiv.Perm.SameCycle σ (F (cutRRepDartMap R hR d)) z ↔
        ∃ e', Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
          (cutRRepDartMap R hR d) e' ∧ F e' = z)
    (hG' : ¬ (cutRRep S hS).2.B.map.IsOuter e →
      ∀ z, Equiv.Perm.SameCycle σ (G (cutRRepDartMap S hS e)) z ↔
        ∃ e', Equiv.Perm.SameCycle S.B.map.toCombinatorialMap.faceSucc
          (cutRRepDartMap S hS e) e' ∧ G e' = z) :
    retainedFace (presentation (cutRRep R hR).2 .right v) d ↔
      retainedFace (presentation (cutRRep S hS).2 .right v') e := by
  rw [cutRRep_retainedFace_iff_selected_image R hR v d,
    cutRRep_retainedFace_iff_selected_image S hS v' e]
  constructor
  · rintro ⟨hd, hcov⟩
    have he : ¬ (cutRRep S hS).2.B.map.IsOuter e := (not_congr hout).mp hd
    refine ⟨he, ?_⟩
    have hleft := (faceOrbit_subset_iff_common σ F hF (cutRRepDartMap R hR)
      R.B.map.toCombinatorialMap.faceSucc
      (selectedDarts (presentation (cutRRep R hR).2 .right v)) d (hF' hd)).mp hcov
    have hright : ∀ z, Equiv.Perm.SameCycle σ
        (G (cutRRepDartMap S hS e)) z →
        z ∈ (G ∘ cutRRepDartMap S hS) ''
          selectedDarts (presentation (cutRRep S hS).2 .right v') := by
      intro z hz
      have hz' : Equiv.Perm.SameCycle σ
          (F (cutRRepDartMap R hR d)) z := by rw [hde]; exact hz
      rw [← himg]
      exact hleft z hz'
    exact (faceOrbit_subset_iff_common σ G hG (cutRRepDartMap S hS)
      S.B.map.toCombinatorialMap.faceSucc
      (selectedDarts (presentation (cutRRep S hS).2 .right v')) e
      (hG' he)).mpr hright
  · rintro ⟨he, hcov⟩
    have hd : ¬ (cutRRep R hR).2.B.map.IsOuter d := (not_congr hout).mpr he
    refine ⟨hd, ?_⟩
    have hright := (faceOrbit_subset_iff_common σ G hG (cutRRepDartMap S hS)
      S.B.map.toCombinatorialMap.faceSucc
      (selectedDarts (presentation (cutRRep S hS).2 .right v')) e (hG' he)).mp hcov
    have hleft : ∀ z, Equiv.Perm.SameCycle σ
        (F (cutRRepDartMap R hR d)) z →
        z ∈ (F ∘ cutRRepDartMap R hR) ''
          selectedDarts (presentation (cutRRep R hR).2 .right v) := by
      intro z hz
      have hz' : Equiv.Perm.SameCycle σ
          (G (cutRRepDartMap S hS e)) z := by rw [← hde]; exact hz
      rw [himg]
      exact hright z hz'
    exact (faceOrbit_subset_iff_common σ F hF (cutRRepDartMap R hR)
      R.B.map.toCombinatorialMap.faceSucc
      (selectedDarts (presentation (cutRRep R hR).2 .right v)) d
      (hF' hd)).mpr hleft

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The common-stage inclusion preserves the entire face orbit of every internal -/
theorem selectedStage_faceOrbit_compat
    {ℓ r n a N : ℕ} (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (d : Fin R.dartCount) (hd : ¬ R.B.map.IsOuter d) :
    ∀ z, Equiv.Perm.SameCycle (kmswMap w N).faceSucc
        (outerSucc_castDart (kmswStage_nextEdge_mono w ha) (I.toEquiv d)) z ↔
      ∃ e, Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc d e ∧
        outerSucc_castDart (kmswStage_nextEdge_mono w ha) (I.toEquiv e) = z := by
  refine faceOrbit_compat_of_commute (kmswMap w N).faceSucc
    (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv)
    R.B.map.toCombinatorialMap.faceSucc d ?_
  intro e he
  have heInner : ¬ R.B.map.IsOuter e := by
    intro ho
    apply hd
    change Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
      R.B.map.outer d
    have ho' : Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.faceSucc
        R.B.map.outer e := ho
    exact ho'.trans he.symm
  have heStage : I.toEquiv e ∉ stageOuterWord w a := by
    intro ho
    have ho' : (kmswStageDirectedMap w a).IsOuter (I.toEquiv e) :=
      (mem_iff_isOuter _ _
        (Section3.kmsw_bdy_source_four_arcs w a).1.1 _).mp ho
    exact heInner ((I.outer_iff e).mp ho')
  change (kmswMap w N).faceSucc
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) (I.toEquiv e)) =
    outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (R.B.map.toCombinatorialMap.faceSucc e))
  rw [directedIso_faceSucc_comm I e]
  exact selectedStage_faceSucc_castDart w ha (I.toEquiv e) heStage

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The later representative's stage isomorphism preserves every face orbit. -/
theorem selectedStage_iso_faceOrbit_compat
    {ℓ r n N : ℕ} (w : ℕ → Fin 3) (S : KMSWMapRep ℓ r n)
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (d : Fin S.dartCount) :
    ∀ z, Equiv.Perm.SameCycle (kmswMap w N).faceSucc (J.toEquiv d) z ↔
      ∃ e, Equiv.Perm.SameCycle S.B.map.toCombinatorialMap.faceSucc d e ∧
        J.toEquiv e = z := by
  apply faceOrbit_compat_of_commute
  intro e he
  exact (directedIso_faceSucc_comm J e).symm

end DirectedDistances.PaperProofs.Section4
