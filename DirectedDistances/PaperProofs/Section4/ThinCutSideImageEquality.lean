module

public import DirectedDistances.PaperProofs.Section4.ThinCutSideColoringTransport
public import DirectedDistances.PaperProofs.Section4.ThinCutRangeCarrierCompatibility
public import DirectedDistances.PaperProofs.Section4.ThinCutMarkedRestrictionCompatibility
import DirectedDistances.PaperProofs.Section4.ThinCutRetainedFaceTransport

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

The common selected prefix identifies the two closed half carriers on the earlier
stage. Their embedded ranges are the later half ranges intersected with that stage. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open scoped Classical

private theorem range_comp_inter_of_transport
    {A B C D E : Type*} (l : A → B) (r : C → D)
    (f : B → E) (g : D → E) (τ : B → D)
    (hg : Function.Injective g) (ht : ∀ b, g (τ b) = f b)
    (h : ∀ b, b ∈ Set.range l ↔ τ b ∈ Set.range r) :
    Set.range (f ∘ l) = Set.range (g ∘ r) ∩ Set.range f := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := (h (l a)).mp ⟨a, rfl⟩
    exact ⟨⟨c, (congrArg g hc).trans (ht (l a))⟩, ⟨l a, rfl⟩⟩
  · rintro ⟨⟨c, hc⟩, ⟨b, hb⟩⟩
    have he : r c = τ b := hg (hc.trans (hb.symm.trans (ht b).symm))
    obtain ⟨a, ha⟩ := (h b).mpr ⟨c, he⟩
    exact ⟨a, (congrArg f ha).trans hb⟩

private theorem image_stage_injective (w : ℕ → Fin 3) {a N : ℕ} (ha : a ≤ N)
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a)) :
    Function.Injective (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘
      I.toEquiv) := by
  intro d e h
  apply I.toEquiv.injective
  apply Prod.ext
  · exact Fin.ext (congrArg (fun z => z.1.val) h)
  · exact congrArg (fun z : StageDart (kmswStage w N).nextEdge => z.2) h

private theorem image_subtype_equiv {A B E : Type*} (f : A → E) (g : B → E)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (U : Set A) (V : Set B) (h : f '' U = g '' V) :
    ∃ e : U ≃ V, ∀ d, f d.1 = g (e d).1 := by
  have hex (d : U) : ∃ e : V, f d.1 = g e.1 := by
    obtain ⟨e, he, hed⟩ := h ▸ Set.mem_image_of_mem f d.2
    exact ⟨⟨e, he⟩, hed.symm⟩
  let e (d : U) : V := Classical.choose (hex d)
  have he (d : U) : f d.1 = g (e d).1 := Classical.choose_spec (hex d)
  have hinj : Function.Injective e := by
    intro d d' hdd'
    apply Subtype.ext
    apply hf
    exact (he d).trans ((congrArg (fun z : V => g z.1) hdd').trans (he d').symm)
  have hsurj : Function.Surjective e := by
    intro z
    obtain ⟨d, hd, hdz⟩ := h ▸ Set.mem_image_of_mem g z.2
    refine ⟨⟨d, hd⟩, Subtype.ext (hg ((he ⟨d, hd⟩).symm.trans hdz))⟩
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, he⟩

private theorem image_selected_list_prefix {A B E : Type*}
    (f : A → E) (g : B → E) (hf : Function.Injective f) (hg : Function.Injective g)
    (U : Set A) (V : Set B) (himg : f '' U = g '' V)
    (l : List A) (r : List B) (m c c' : ℕ) (hc : c < m)
    (hl : ∀ i, (∃ d : U, l[i]? = some d.1) ↔ i < c)
    (hr : ∀ i, (∃ d : V, r[i]? = some d.1) ↔ i < c')
    (hp : ∀ i < m, ∃ d e, l[i]? = some d ∧ r[i]? = some e ∧ f d = g e) :
    ∀ (i : ℕ) (z : E), (∃ d : U, l[i]? = some d.1 ∧ f d.1 = z) ↔
      (∃ e : V, r[i]? = some e.1 ∧ g e.1 = z) := by
  have hsmall (i : ℕ) (hi : i < m) : i < c ↔ i < c' := by
    obtain ⟨d, e, hd, he, hde⟩ := hp i hi
    have hsel := selectedDarts_iff_of_image_eq f g hf hg himg d e hde
    constructor
    · intro h
      obtain ⟨d', hd'⟩ := (hl i).mpr h
      have hdsel : d ∈ U := Option.some.inj (hd'.symm.trans hd) ▸ d'.2
      exact (hr i).mp ⟨⟨e, hsel.mp hdsel⟩, he⟩
    · intro h
      obtain ⟨e', he'⟩ := (hr i).mpr h
      have hesel : e ∈ V := Option.some.inj (he'.symm.trans he) ▸ e'.2
      exact (hl i).mp ⟨⟨d, hsel.mpr hesel⟩, hd⟩
  have hcc : c = c' := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact (Nat.lt_irrefl c) ((hsmall c hc).mpr hlt)
    · exact (Nat.lt_irrefl c') ((hsmall c' (lt_trans hgt hc)).mp hgt)
  intro i z
  by_cases hi : i < c
  · obtain ⟨d, e, hd, he, hde⟩ := hp i (lt_trans hi hc)
    constructor
    · rintro ⟨d', hd', hdz⟩
      have hdd : d'.1 = d := Option.some.inj (hd'.symm.trans hd)
      have hesel := (selectedDarts_iff_of_image_eq f g hf hg himg d e hde).mp
        (hdd ▸ d'.2)
      exact ⟨⟨e, hesel⟩, he, hde.symm.trans ((congrArg f hdd).symm.trans hdz)⟩
    · rintro ⟨e', he', hez⟩
      have hee : e'.1 = e := Option.some.inj (he'.symm.trans he)
      have hdsel := (selectedDarts_iff_of_image_eq f g hf hg himg d e hde).mpr
        (hee ▸ e'.2)
      exact ⟨⟨d, hdsel⟩, hd, hde.trans ((congrArg g hee).symm.trans hez)⟩
  · constructor
    · rintro ⟨d, hd, _⟩
      exact (hi ((hl i).mp ⟨d, hd⟩)).elim
    · rintro ⟨e, he, _⟩
      exact (hi (hcc ▸ (hr i).mp ⟨e, he⟩)).elim

private theorem image_boundary_prefix {A B C D E : Type*}
    (l : List A) (r : List B) (P : List C) (Q : List D)
    (u : A → C) (v : B → D) (f : C → E) (g : D → E)
    (hl : l.map u = P) (hr : r.map v = Q) (m : ℕ)
    (hp : ∀ i < m, ∃ d e, P[i]? = some d ∧ Q[i]? = some e ∧ f d = g e) :
    ∀ i < m, ∃ d e, l[i]? = some d ∧ r[i]? = some e ∧ f (u d) = g (v e) := by
  intro i hi
  obtain ⟨d, e, hd, he, hde⟩ := hp i hi
  rw [← hl, List.getElem?_map] at hd
  rw [← hr, List.getElem?_map] at he
  obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
  obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.mp he
  exact ⟨d', e', hd', he', hde⟩

private theorem image_outer_iff {D E : Type*} [Fintype D] [DecidableEq D]
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (f : D → E) (hf : Function.Injective f) (σ : E → E)
    (hσ : ∀ d, f (B.map.edgeInv d) = σ (f d)) (l r : List E)
    (hl : B.leftPath.darts.map f = l) (hr : B.rightPath.darts.map f = r) (d : D) :
    B.map.IsOuter d ↔ f d ∈ l ∨ ∃ e ∈ r, f d = σ e := by
  rw [isOuter_iff_mem_left_or_reverse_right_boundary]
  constructor
  · rintro (hd | ⟨e, he, hde⟩)
    · exact Or.inl (hl ▸ List.mem_map.mpr ⟨d, hd, rfl⟩)
    · exact Or.inr ⟨f e, hr ▸ List.mem_map.mpr ⟨e, he, rfl⟩,
        (congrArg f hde).trans (hσ e)⟩
  · rintro (hd | ⟨e, he, hde⟩)
    · rw [← hl] at hd
      obtain ⟨e, he, hed⟩ := List.mem_map.mp hd
      exact Or.inl (hf hed ▸ he)
    · rw [← hr] at he
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp he
      exact Or.inr ⟨z, hz, hf (hde.trans (hσ z).symm)⟩

private theorem image_right_arc_iff {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    (∃ e ∈ B.rightPath.darts, d = B.map.edgeInv e) ↔ d ∈ pathCutRightOuterArc B := by
  rw [mem_pathCutRightOuterArc_iff]
  constructor
  · rintro ⟨e, he, hde⟩
    exact List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, hde.symm⟩
  · intro h
    obtain ⟨e, he, hed⟩ := List.mem_map.mp h
    exact ⟨e, List.mem_reverse.mp he, hed.symm⟩

private theorem image_cutR_outer {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutRRep R hR).2.dartCount) :
    (cutRRep R hR).2.B.map.IsOuter d ↔
      cutRRepDartMap R hR d ∈ (selectedGeodesicOfLen R.B x hR).darts ∨
      cutRRepDartMap R hR d ∈ pathCutRightOuterArc R.B := by
  have h := image_outer_iff (cutRRep R hR).2.B (cutRRepDartMap R hR)
    (cutRRep_embedding_fields R hR).1 R.B.map.edgeInv
    (cutRRep_embedding_fields R hR).2.2.1 _ _
    (cutRRep_boundaryDarts_map R hR).2 (cutRRep_boundaryDarts_map R hR).1 d
  exact h.trans (or_congr Iff.rfl (image_right_arc_iff R.B _))

private theorem image_cutL_outer {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutLRep R hR).2.dartCount) :
    (cutLRep R hR).2.B.map.IsOuter d ↔
      cutLRepDartMap R hR d ∈ pathCutLeftOuterArc R.B ∨
      ∃ e ∈ (selectedGeodesicOfLen R.B x hR).darts,
        cutLRepDartMap R hR d = R.B.map.edgeInv e := by
  have h := image_outer_iff (cutLRep R hR).2.B (cutLRepDartMap R hR)
    (cutLRep_embedding_fields R hR).1 R.B.map.edgeInv
    (cutLRep_embedding_fields R hR).2.2.1 _ _
    (cutLRep_boundaryDarts_map R hR).1 (cutLRep_boundaryDarts_map R hR).2 d
  exact h.trans (or_congr (mem_pathCutLeftOuterArc_iff R.B _).symm Iff.rfl)

private theorem image_stage_tail_side {ℓ r n t : ℕ}
    (w : ℕ → Fin 3) (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (d : Fin R.dartCount) : R.B.map.tail d ↔ (I.toEquiv d).2 = false := by
  have hp : (kmswStage w t).present (I.toEquiv d).1.val = true := by
    have hn : ¬ (kmswStageDirectedMap w t).missing (I.toEquiv d) := by
      intro h
      exact R.B.noMissingDarts d ((I.missing_iff d).mp h)
    change ¬ (kmswStage w t).present (I.toEquiv d).1.val = false at hn
    cases he : (kmswStage w t).present (I.toEquiv d).1.val <;> simp_all
  rw [← I.tail_iff]
  change (_ ∧ _) ↔ _
  exact ⟨And.right, fun h => ⟨hp, h⟩⟩

private theorem image_cutR_nonouter {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutRRep R hR).2.dartCount)
    (hd : ¬ (cutRRep R hR).2.B.map.IsOuter d) :
    ¬ R.B.map.IsOuter (cutRRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hb : (I.toEquiv d).1 ∉ pathCutRightHalfBoundaryDarts R.B P := by
    intro h
    exact hd ((I.outer_iff d).mp
      ((pathCutRightHalfMarked_isOuter_iff R.B P (I.toEquiv d)).mpr h))
  exact (pathCutRightHalf_inner_face_contained R.B P (I.toEquiv d).2 hb).1

private theorem image_cutL_nonouter {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutLRep R hR).2.dartCount)
    (hd : ¬ (cutLRep R hR).2.B.map.IsOuter d) :
    ¬ R.B.map.IsOuter (cutLRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have hb : (I.toEquiv d).1 ∉ pathCutLeftHalfBoundaryDarts R.B P := by
    intro h
    exact hd ((I.outer_iff d).mp
      ((pathCutLeftHalfMarked_isOuter_iff R.B P (I.toEquiv d)).mpr h))
  exact (pathCutLeftHalf_inner_face_contained R.B P (I.toEquiv d).2 hb).1

section StageRanges
variable {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)

include hP

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The embedded left half range is the later range restricted to the earlier stage. -/
theorem cutLRepDartMap_stage_range :
    Set.range ((outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
      cutLRepDartMap R hR) =
      Set.range (J.toEquiv ∘ cutLRepDartMap S hS) ∩
        Set.range (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) := by
  apply range_comp_inter_of_transport _ _ _ _
    (selectedStageDartTransport w ha R S I J) J.toEquiv.injective
  · intro e
    exact J.toEquiv.apply_symm_apply _
  · intro e
    rw [cutLRepDartMap_range, cutLRepDartMap_range]
    exact selectedStageDartTransport_leftHalfDarts_iff
      w ha R hR S hS I J fv gv hP e

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The embedded right half range is the later range restricted to the earlier stage. -/
theorem cutRRepDartMap_stage_range :
    Set.range ((outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
      cutRRepDartMap R hR) =
      Set.range (J.toEquiv ∘ cutRRepDartMap S hS) ∩
        Set.range (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) := by
  apply range_comp_inter_of_transport _ _ _ _
    (selectedStageDartTransport w ha R S I J) J.toEquiv.injective
  · intro e
    exact J.toEquiv.apply_symm_apply _
  · intro e
    rw [cutRRepDartMap_range, cutRRepDartMap_range]
    exact selectedStageDartTransport_rightHalfDarts_iff
      w ha R hR S hS I J fv gv hP e

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Right-half outer darts correspond across the common-stage embedding. -/
theorem cutRRep_isOuter_stage_iff
    (d : Fin (cutRRep R hR).2.dartCount)
    (e : Fin (cutRRep S hS).2.dartCount)
    (hde : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutRRepDartMap R hR d)) =
        J.toEquiv (cutRRepDartMap S hS e)) :
    (cutRRep R hR).2.B.map.IsOuter d ↔ (cutRRep S hS).2.B.map.IsOuter e := by
  let τ := selectedStageDartTransport w ha R S I J
  let d₀ := cutRRepDartMap R hR d
  let e₀ := cutRRepDartMap S hS e
  have hτ : τ d₀ = e₀ := by
    apply J.toEquiv.injective
    exact (J.toEquiv.apply_symm_apply _).trans hde
  have hp : d₀ ∈ (selectedGeodesicOfLen R.B x hR).darts ↔
      e₀ ∈ (selectedGeodesicOfLen S.B x hS).darts := by
    rw [← hτ]
    exact ⟨selectedStageDartTransport_pathDart w ha R hR S hS I J fv gv hP d₀,
      selectedStageDartTransport_pathDart_reflect w ha R hR S hS I J fv gv hP d₀⟩
  have hr : d₀ ∈ pathCutRightOuterArc R.B ↔ e₀ ∈ pathCutRightOuterArc S.B := by
    constructor
    · intro h
      rw [← hτ]
      exact selectedStageDartTransport_rightOuterArc w ha R S I J d₀ h
    · intro h
      refine ⟨R.B.noMissingDarts d₀, ?_, ?_⟩
      · intro ht
        have hdside := (image_stage_tail_side w R I d₀).mp ht
        have heside : (J.toEquiv e₀).2 = false := by
          rw [← hde]
          exact hdside
        exact h.2.1 ((image_stage_tail_side w S J e₀).mpr heside)
      · by_contra hn
        have ho : S.B.map.IsOuter (τ d₀) := by rw [hτ]; exact h.2.2
        exact selectedStageDartTransport_not_outer w ha R S I J d₀ hn ho
  rw [image_cutR_outer R hR d, image_cutR_outer S hS e]
  exact or_congr hp hr




theorem cutLRep_isOuter_stage_reflect
    (d : Fin (cutLRep R hR).2.dartCount)
    (e : Fin (cutLRep S hS).2.dartCount)
    (hde : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutLRepDartMap R hR d)) =
        J.toEquiv (cutLRepDartMap S hS e))
    (he : (cutLRep S hS).2.B.map.IsOuter e) :
    (cutLRep R hR).2.B.map.IsOuter d := by
  let τ := selectedStageDartTransport w ha R S I J
  let d₀ := cutLRepDartMap R hR d
  let e₀ := cutLRepDartMap S hS e
  have hτ : τ d₀ = e₀ := by
    apply J.toEquiv.injective
    exact (J.toEquiv.apply_symm_apply _).trans hde
  apply (image_cutL_outer R hR d).mpr
  rcases (image_cutL_outer S hS e).mp he with hl | ⟨z, hz, hez⟩
  · left
    refine ⟨R.B.noMissingDarts d₀, ?_, ?_⟩
    · have heside := (image_stage_tail_side w S J e₀).mp hl.2.1
      have hdside : (I.toEquiv d₀).2 = false := by
        have hh := congrArg (fun z : StageDart (kmswStage w N).nextEdge => z.2) hde
        exact hh.trans heside
      exact (image_stage_tail_side w R I d₀).mpr hdside
    · by_contra hn
      have ho : S.B.map.IsOuter (τ d₀) := by rw [hτ]; exact hl.2.2
      exact selectedStageDartTransport_not_outer w ha R S I J d₀ hn ho
  · right
    let z₀ := R.B.map.edgeInv d₀
    have hzτ : τ z₀ = z := by
      calc
        τ z₀ = S.B.map.edgeInv (τ d₀) :=
          selectedStageDartTransport_edgeInv w ha R S I J d₀
        _ = S.B.map.edgeInv (S.B.map.edgeInv z) := congrArg S.B.map.edgeInv
          (hτ.trans hez)
        _ = z := S.B.map.edgeInv_invol z
    have hz₀ : z₀ ∈ (selectedGeodesicOfLen R.B x hR).darts := by
      apply selectedStageDartTransport_pathDart_reflect w ha R hR S hS I J fv gv hP
      change τ z₀ ∈ _
      rw [hzτ]
      exact hz
    exact ⟨z₀, hz₀, (R.B.map.edgeInv_invol d₀).symm⟩

end StageRanges

private theorem image_path_vertices_reach {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {x y : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M x y n) (i d : ℕ) (hid : i + d ≤ n) :
    Relation.ReflTransGen M.directedStep
      (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
      (P.vertices.get ⟨i + d, by rw [P.vertices_length]; omega⟩) := by
  induction d with
  | zero => exact Relation.ReflTransGen.refl
  | succ d ih =>
      have hs := P.edge_step ⟨i + d, by rw [P.darts_length]; omega⟩
      apply (ih (by omega)).tail
      exact ⟨P.darts.get ⟨i + d, by rw [P.darts_length]; omega⟩,
        hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩


private theorem image_stage_reachable_iff (w : ℕ → Fin 3) (t : ℕ)
    (v z : MapVertex (kmswStageDirectedMap w t)) :
    Relation.ReflTransGen (kmswStageDirectedMap w t).directedStep v z ↔
      Reachable (stageMapVertex w t v) (stageMapVertex w t z) := by
  constructor
  · intro h
    induction h with
    | refl => exact Reachable.rfl
    | tail _ hstep ih =>
        obtain ⟨e⟩ := (stageMap_directedStep_iff w t _ _).mp hstep
        exact ih.trans e.reachable
  · rintro ⟨p⟩
    obtain ⟨P⟩ := (stageMap_path_iff w t p.length v z).mpr ⟨p, rfl⟩
    have h := image_path_vertices_reach P 0 p.length (by omega)
    simpa only [Nat.zero_add, P.start_vertex, P.end_vertex] using h

private theorem image_ancestor_record_iff
    {ℓ r n : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (a : ThinMapSide) (v z : MapVertex R.B.map)
    (hv : (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id =
      (recordVertex w u).id) :
    z ∈ ancestors (presentation R a v) ↔
      Reachable
        (⟨(stageMapVertex w t (cutMapIsoVertexEquiv I z)).id⟩ : PresentVertex w)
        (recordVertex w u) := by
  change Relation.ReflTransGen R.B.map.directedStep z v ↔ _
  rw [cutMapIsoVertexEquiv_reachable_iff I, image_stage_reachable_iff]
  have he : stageMapVertex w t (cutMapIsoVertexEquiv I v) =
      (⟨(recordVertex w u).id⟩ : StagePresentVertex w t) :=
    congrArg StagePresentVertex.mk hv
  rw [he]
  exact record_ancestor_reachable_iff_stage w u t _ hut

private theorem image_selectedDarts_record_iff
    {ℓ r n : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (a : ThinMapSide) (v : MapVertex R.B.map)
    (hv : (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id =
      (recordVertex w u).id) (e : Fin R.dartCount) :
    e ∈ selectedDarts (presentation R a v) ↔
      Reachable (⟨edgeWest w (I.toEquiv e).1.val⟩ : PresentVertex w) (recordVertex w u) ∧
      Reachable (⟨edgeEast w (I.toEquiv e).1.val⟩ : PresentVertex w)
        (recordVertex w u) := by
  change (_ ∈ ancestors _ ∧ _ ∈ ancestors _) ↔ _
  rw [image_ancestor_record_iff w t u hut R I a _ _ hv,
    image_ancestor_record_iff w t u hut R I a _ _ hv]
  rw [(cutMapIsoVertexEquiv_endpoints I e).1,
    (cutMapIsoVertexEquiv_endpoints I e).2]
  change (Reachable (⟨stageEndpoint (kmswStage w t) (I.toEquiv e)⟩ : PresentVertex w) _ ∧
    Reachable (⟨stageEndpoint (kmswStage w t) (edgeFlip _ (I.toEquiv e))⟩ :
      PresentVertex w) _) ↔ _
  change (Reachable (⟨if (I.toEquiv e).2 then (kmswStage w t).east (I.toEquiv e).1.val
      else (kmswStage w t).west (I.toEquiv e).1.val⟩ : PresentVertex w) _ ∧
    Reachable (⟨if !(I.toEquiv e).2 then (kmswStage w t).east (I.toEquiv e).1.val
      else (kmswStage w t).west (I.toEquiv e).1.val⟩ : PresentVertex w) _) ↔ _
  obtain ⟨hw, he⟩ := edge_endpoints_eq w (I.toEquiv e).1.isLt
  cases hb : (I.toEquiv e).2 with
  | false => simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, hw, he]
  | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hw, he, and_comm]


private theorem image_selectedDarts_record_stage_eq
    {ℓ r n ℓ' r' n' a N : ℕ}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (hL : ∀ j, 0 ≤ L w j) (hRneg : ∀ b : ℤ, ∃ j, KMSW.R w j ≤ b)
    (u : ℕ) (hu : u ≤ a)
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (side : ThinMapSide) (v : MapVertex R.B.map) (v' : MapVertex S.B.map)
    (hv : (stageMapVertex w a (cutMapIsoVertexEquiv I v)).id =
      (recordVertex w u).id)
    (hv' : (stageMapVertex w N (cutMapIsoVertexEquiv J v')).id =
      (recordVertex w u).id) :
    (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ''
        selectedDarts (presentation R side v) =
      J.toEquiv '' selectedDarts (presentation S side v') := by
  ext z
  constructor
  · rintro ⟨e, he, rfl⟩
    let d := selectedStageDartTransport w ha R S I J e
    have hd : J.toEquiv d = outerSucc_castDart
        (kmswStage_nextEdge_mono w ha) (I.toEquiv e) := J.toEquiv.apply_symm_apply _
    refine ⟨d, ?_, hd⟩
    apply (image_selectedDarts_record_iff w N u (hu.trans ha) S J side v' hv' d).mpr
    have hh := (image_selectedDarts_record_iff w a u hu R I side v hv e).mp he
    rw [hd]
    exact hh
  · rintro ⟨e, he, rfl⟩
    have hh := (image_selectedDarts_record_iff w N u (hu.trans ha) S J side v' hv' e).mp he
    have hb := (record_ancestor_geometric_edge_in_stage w hL hRneg u a
      (J.toEquiv e).1.val hu hh.2).1
    let d : StageDart (kmswStage w a).nextEdge := (⟨(J.toEquiv e).1.val, hb⟩,
      (J.toEquiv e).2)
    let c := I.toEquiv.symm d
    have hc : I.toEquiv c = d := I.toEquiv.apply_symm_apply _
    refine ⟨c, ?_, ?_⟩
    · apply (image_selectedDarts_record_iff w a u hu R I side v hv c).mpr
      rw [hc]
      exact hh
    · change outerSucc_castDart (kmswStage_nextEdge_mono w ha) (I.toEquiv c) = _
      rw [hc]
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl

private theorem image_comp_eq_inter
    {A B E : Type*} (l : A → B) (f : B → E) (hf : Function.Injective f)
    (U : Set A) (X : Set B)
    (h : ∀ b, b ∈ l '' U ↔ b ∈ Set.range l ∧ b ∈ X) :
    (f ∘ l) '' U = Set.range (f ∘ l) ∩ f '' X := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, ⟨l a, ((h (l a)).mp ⟨a, ha, rfl⟩).2, rfl⟩⟩
  · rintro ⟨⟨a, rfl⟩, ⟨b, hb, he⟩⟩
    have hba : b = l a := hf he
    obtain ⟨c, hc, hce⟩ := (h (l a)).mpr ⟨⟨a, rfl⟩, hba ▸ hb⟩
    exact ⟨c, hc, congrArg f hce⟩

private theorem inter_eq_of_range_eq
    {E : Type*} (A B C X Y : Set E) (hAB : A = B ∩ C)
    (hXY : X = Y) (hXC : X ⊆ C) : A ∩ X = B ∩ Y := by
  rw [hAB, ← hXY]
  ext z
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hXC h.2⟩, h.2⟩⟩

private theorem image_ancestor_tail_or_target (P : HalfTruncationRep)
    (v : ancestors P) :
    v.1 = P.target ∨ ∃ d : selectedDarts P,
      dartTailVertex P.rep.B.map d.1 = v.1 := by
  rcases v.2.cases_head with h | ⟨z, hz, hzt⟩
  · exact Or.inl h
  · obtain ⟨d, _, _, hd, he⟩ := hz
    have ht : dartTailVertex P.rep.B.map d = v.1 := hd
    have hh : dartHeadVertex P.rep.B.map d = z := he
    refine Or.inr ⟨⟨d, ?_, ?_⟩, ht⟩
    · rw [ht]
      exact v.2
    · rw [hh]
      exact hzt

private theorem image_ancestors_eq {E V : Type*} (P Q : HalfTruncationRep)
    (f : Fin P.rep.dartCount → E) (g : Fin Q.rep.dartCount → E)
    (F : MapVertex P.rep.B.map → V) (G : MapVertex Q.rep.B.map → V)
    (tail : E → V)
    (hf : ∀ d, F (dartTailVertex P.rep.B.map d) = tail (f d))
    (hg : ∀ d, G (dartTailVertex Q.rep.B.map d) = tail (g d))
    (ht : F P.target = G Q.target)
    (himg : f '' selectedDarts P = g '' selectedDarts Q) :
    F '' ancestors P = G '' ancestors Q := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases image_ancestor_tail_or_target P ⟨v, hv⟩ with h | ⟨d, hd⟩
    · exact ⟨Q.target, Relation.ReflTransGen.refl, ht.symm.trans (congrArg F h).symm⟩
    · obtain ⟨e, he, hed⟩ := himg ▸ Set.mem_image_of_mem f d.2
      exact ⟨dartTailVertex Q.rep.B.map e, he.1,
        (hg e).trans ((congrArg tail hed).trans ((hf d.1).symm.trans
          (congrArg F hd)))⟩
  · rintro ⟨v, hv, rfl⟩
    rcases image_ancestor_tail_or_target Q ⟨v, hv⟩ with h | ⟨d, hd⟩
    · exact ⟨P.target, Relation.ReflTransGen.refl, ht.trans (congrArg G h).symm⟩
    · obtain ⟨e, he, hed⟩ := himg ▸ Set.mem_image_of_mem g d.2
      exact ⟨dartTailVertex P.rep.B.map e, he.1,
        (hf e).trans ((congrArg tail hed).trans ((hg d.1).symm.trans
          (congrArg G hd)))⟩

private theorem image_stage_vertex_injective {ℓ r n : ℕ}
    (w : ℕ → Fin 3) (t : ℕ) (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t)) :
    Function.Injective (fun v => (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id) := by
  intro v z h
  apply (cutMapIsoVertexEquiv I).injective
  apply stageMapVertex_injective w t
  exact congrArg StagePresentVertex.mk h

private theorem image_stage_vertex_tail {ℓ r n : ℕ}
    (w : ℕ → Fin 3) (t : ℕ) (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (d : Fin R.dartCount) :
    (stageMapVertex w t (cutMapIsoVertexEquiv I (dartTailVertex R.B.map d))).id =
      if (I.toEquiv d).2 then edgeEast w (I.toEquiv d).1.val
      else edgeWest w (I.toEquiv d).1.val := by
  rw [(cutMapIsoVertexEquiv_endpoints I d).1, stageMapVertex_tail]
  unfold stageEndpoint
  rw [(edge_endpoints_eq w (I.toEquiv d).1.isLt).1,
    (edge_endpoints_eq w (I.toEquiv d).1.isLt).2]

private theorem image_cutL_tail {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutLRep R hR).2.dartCount) :
    cutLRepVertexMap R hR (dartTailVertex (cutLRep R hR).2.B.map d) =
      dartTailVertex R.B.map (cutLRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  exact (congrArg (pathCutLeftHalfVertexMap R.B P)
    (I.vertexEquiv_dartTailVertex d)).trans
      (pathCutLeftHalfVertexMap_dartTailVertex R.B P (I.toEquiv d))

private theorem image_cutR_tail {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutRRep R hR).2.dartCount) :
    cutRRepVertexMap R hR (dartTailVertex (cutRRep R hR).2.B.map d) =
      dartTailVertex R.B.map (cutRRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  exact (congrArg (pathCutRightHalfVertexMap R.B P)
    (I.vertexEquiv_dartTailVertex d)).trans
      (pathCutRightHalfVertexMap_dartTailVertex R.B P (I.toEquiv d))

private theorem image_root_forward {E V : Type*} (P Q : HalfTruncationRep)
    (f : Fin P.rep.dartCount → E) (g : Fin Q.rep.dartCount → E)
    (F : MapVertex P.rep.B.map → V) (G : MapVertex Q.rep.B.map → V)
    (head : E → V) (hF : Function.Injective F)
    (hf : ∀ d, F (dartHeadVertex P.rep.B.map d) = head (f d))
    (hg : ∀ d, G (dartHeadVertex Q.rep.B.map d) = head (g d))
    (ho : ∀ d e, f d = g e → (P.rep.B.map.tail d ↔ Q.rep.B.map.tail e))
    (himg : f '' selectedDarts P = g '' selectedDarts Q)
    (v : ancestors P) (z : ancestors Q) (hvz : F v.1 = G z.1)
    (hv : v.1 = P.rep.B.source) : z.1 = Q.rep.B.source := by
  apply Q.rep.B.source_unique
  rintro ⟨b, e, hm, ht, hb, hz⟩
  change dartTailVertex Q.rep.B.map e = b at hb
  change dartHeadVertex Q.rep.B.map e = z.1 at hz
  have he : e ∈ selectedDarts Q := by
    constructor
    · rw [hb]
      exact Relation.ReflTransGen.head ⟨e, hm, ht, hb, hz⟩ z.2
    · rw [hz]
      exact z.2
  obtain ⟨d, _hd, hde⟩ := himg ▸ Set.mem_image_of_mem g he
  have hhead : dartHeadVertex P.rep.B.map d = v.1 := by
    apply hF
    exact (hf d).trans ((congrArg head hde).trans
      ((hg e).symm.trans ((congrArg G hz).trans hvz.symm)))
  exact P.rep.B.isSource ⟨dartTailVertex P.rep.B.map d, d,
    P.rep.B.noMissingDarts d, (ho d e hde).mpr ht, rfl, hhead.trans hv⟩

private theorem image_stage_vertex_head {ℓ r n : ℕ}
    (w : ℕ → Fin 3) (t : ℕ) (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (d : Fin R.dartCount) :
    (stageMapVertex w t (cutMapIsoVertexEquiv I (dartHeadVertex R.B.map d))).id =
      if (I.toEquiv d).2 then edgeWest w (I.toEquiv d).1.val
      else edgeEast w (I.toEquiv d).1.val := by
  change (stageMapVertex w t (cutMapIsoVertexEquiv I
    (dartTailVertex R.B.map (R.B.map.edgeInv d)))).id = _
  rw [image_stage_vertex_tail, I.edgeInv_comm]
  change (if !(I.toEquiv d).2 then _ else _) = _
  cases (I.toEquiv d).2 <;> rfl

private theorem image_cutL_head {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutLRep R hR).2.dartCount) :
    cutLRepVertexMap R hR (dartHeadVertex (cutLRep R hR).2.B.map d) =
      dartHeadVertex R.B.map (cutLRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  exact (congrArg (pathCutLeftHalfVertexMap R.B P)
    (I.vertexEquiv_dartHeadVertex d)).trans
      (pathCutLeftHalfVertexMap_dartHeadVertex R.B P (I.toEquiv d))

private theorem image_cutR_head {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (d : Fin (cutRRep R hR).2.dartCount) :
    cutRRepVertexMap R hR (dartHeadVertex (cutRRep R hR).2.B.map d) =
      dartHeadVertex R.B.map (cutRRepDartMap R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutRightHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  exact (congrArg (pathCutRightHalfVertexMap R.B P)
    (I.vertexEquiv_dartHeadVertex d)).trans
      (pathCutRightHalfVertexMap_dartHeadVertex R.B P (I.toEquiv d))

private theorem image_mark_index_iff {A B E : Type*}
    (f : A → E) (g : B → E) (hf : Function.Injective f) (hg : Function.Injective g)
    (U : Set A) (V : Set B) (l : List A) (r : List B)
    (h : ∀ (i : ℕ) z, (∃ d : U, l[i]? = some d.1 ∧ f d.1 = z) ↔
      (∃ e : V, r[i]? = some e.1 ∧ g e.1 = z))
    (d : U) (e : V) (hde : f d.1 = g e.1) (i : ℕ) :
    l[i]? = some d.1 ↔ r[i]? = some e.1 := by
  constructor
  · intro hd
    obtain ⟨e', he', he⟩ := (h i (f d.1)).mp ⟨d, hd, rfl⟩
    exact hg (he.trans hde) ▸ he'
  · intro he
    obtain ⟨d', hd', hd⟩ := (h i (g e.1)).mpr ⟨e, he, rfl⟩
    exact hf (hd.trans hde.symm) ▸ hd'

section StageImages
variable {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)

variable (hL : ∀ j, 0 ≤ L w j) (hRneg : ∀ b : ℤ, ∃ j, KMSW.R w j ≤ b)

include hP hL hRneg

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected left-half dart images agree at a common earlier record target. -/
theorem cutLRep_selectedDarts_stage_image_eq
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id = (recordVertex w u).id) :
    ((outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
        cutLRepDartMap R hR) '' selectedDarts (presentation (cutLRep R hR).2 .left v) =
      (J.toEquiv ∘ cutLRepDartMap S hS) ''
        selectedDarts (presentation (cutLRep S hS).2 .left v') := by
  let fd := outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv
  have hf : Function.Injective fd := by
    intro e d hed
    apply I.toEquiv.injective
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z => z.1.val) hed)
    · exact congrArg (fun z : StageDart (kmswStage w N).nextEdge => z.2) hed
  rw [image_comp_eq_inter (cutLRepDartMap R hR) fd hf _ _
    (cutLRep_selectedDarts_image_iff R hR v)]
  rw [image_comp_eq_inter (cutLRepDartMap S hS) J.toEquiv J.toEquiv.injective _ _
    (cutLRep_selectedDarts_image_iff S hS v')]
  apply inter_eq_of_range_eq _ _ (Set.range fd) _ _
  · exact cutLRepDartMap_stage_range w ha R hR S hS I J fv gv hP
  · exact image_selectedDarts_record_stage_eq w ha hL hRneg u hu R S I J .left
      (cutLRepVertexMap R hR v) (cutLRepVertexMap S hS v') hv hv'
  · rintro z ⟨e, _, rfl⟩
    exact ⟨e, rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected right-half dart images agree at a common earlier record target. -/
theorem cutRRep_selectedDarts_stage_image_eq
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id = (recordVertex w u).id) :
    ((outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
        cutRRepDartMap R hR) '' selectedDarts (presentation (cutRRep R hR).2 .right v) =
      (J.toEquiv ∘ cutRRepDartMap S hS) ''
        selectedDarts (presentation (cutRRep S hS).2 .right v') := by
  let fd := outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv
  have hf : Function.Injective fd := by
    intro e d hed
    apply I.toEquiv.injective
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z => z.1.val) hed)
    · exact congrArg (fun z : StageDart (kmswStage w N).nextEdge => z.2) hed
  rw [image_comp_eq_inter (cutRRepDartMap R hR) fd hf _ _
    (cutRRep_selectedDarts_image_iff R hR v)]
  rw [image_comp_eq_inter (cutRRepDartMap S hS) J.toEquiv J.toEquiv.injective _ _
    (cutRRep_selectedDarts_image_iff S hS v')]
  apply inter_eq_of_range_eq _ _ (Set.range fd) _ _
  · exact cutRRepDartMap_stage_range w ha R hR S hS I J fv gv hP
  · exact image_selectedDarts_record_stage_eq w ha hL hRneg u hu R S I J .right
      (cutRRepVertexMap R hR v) (cutRRepVertexMap S hS v') hv hv'
  · rintro z ⟨e, _, rfl⟩
    exact ⟨e, rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The ancestor vertices correspond by their permanent IDs, including the target. -/
theorem cutLRep_ancestors_stage_equiv
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id = (recordVertex w u).id) :
    ∃ e : ancestors (presentation (cutLRep R hR).2 .left v) ≃
        ancestors (presentation (cutLRep S hS).2 .left v'),
      ∀ z, (stageMapVertex w a
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR z.1))).id =
          (stageMapVertex w N
            (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS (e z).1))).id := by
  let F := fun z => (stageMapVertex w a
    (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR z))).id
  let G := fun z => (stageMapVertex w N
    (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS z))).id
  apply image_subtype_equiv F G
    ((image_stage_vertex_injective w a R I).comp (cutLRep_embedding_fields R hR).2.1)
    ((image_stage_vertex_injective w N S J).comp (cutLRep_embedding_fields S hS).2.1)
  apply image_ancestors_eq (presentation (cutLRep R hR).2 .left v)
    (presentation (cutLRep S hS).2 .left v')
    ((outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
      cutLRepDartMap R hR) (J.toEquiv ∘ cutLRepDartMap S hS) F G
    (fun d => if d.2 then edgeEast w d.1.val else edgeWest w d.1.val)
  · intro d
    change (stageMapVertex w a (cutMapIsoVertexEquiv I
      (cutLRepVertexMap R hR (dartTailVertex (cutLRep R hR).2.B.map d)))).id = _
    rw [image_cutL_tail, image_stage_vertex_tail]
    rfl
  · intro d
    change (stageMapVertex w N (cutMapIsoVertexEquiv J
      (cutLRepVertexMap S hS (dartTailVertex (cutLRep S hS).2.B.map d)))).id = _
    rw [image_cutL_tail, image_stage_vertex_tail]
    rfl
  · exact hv.trans hv'.symm
  · exact cutLRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The ancestor vertices correspond by their permanent IDs, including the target. -/
theorem cutRRep_ancestors_stage_equiv
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id = (recordVertex w u).id) :
    ∃ e : ancestors (presentation (cutRRep R hR).2 .right v) ≃
        ancestors (presentation (cutRRep S hS).2 .right v'),
      ∀ z, (stageMapVertex w a
        (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z.1))).id =
          (stageMapVertex w N
            (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS (e z).1))).id := by
  let F := fun z => (stageMapVertex w a
    (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z))).id
  let G := fun z => (stageMapVertex w N
    (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS z))).id
  apply image_subtype_equiv F G
    ((image_stage_vertex_injective w a R I).comp (cutRRep_embedding_fields R hR).2.1)
    ((image_stage_vertex_injective w N S J).comp (cutRRep_embedding_fields S hS).2.1)
  apply image_ancestors_eq (presentation (cutRRep R hR).2 .right v)
    (presentation (cutRRep S hS).2 .right v')
    ((outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
      cutRRepDartMap R hR) (J.toEquiv ∘ cutRRepDartMap S hS) F G
    (fun d => if d.2 then edgeEast w d.1.val else edgeWest w d.1.val)
  · intro d
    change (stageMapVertex w a (cutMapIsoVertexEquiv I
      (cutRRepVertexMap R hR (dartTailVertex (cutRRep R hR).2.B.map d)))).id = _
    rw [image_cutR_tail, image_stage_vertex_tail]
    rfl
  · intro d
    change (stageMapVertex w N (cutMapIsoVertexEquiv J
      (cutRRepVertexMap S hS (dartTailVertex (cutRRep S hS).2.B.map d)))).id = _
    rw [image_cutR_tail, image_stage_vertex_tail]
    rfl
  · exact hv.trans hv'.symm
  · exact cutRRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Matching ancestor vertices preserve root, target and selected-dart incidence. -/
theorem cutLRep_ancestor_marks_stage_iff
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id = (recordVertex w u).id)
    (z : ancestors (presentation (cutLRep R hR).2 .left v))
    (z' : ancestors (presentation (cutLRep S hS).2 .left v'))
    (hz : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR z.1))).id =
        (stageMapVertex w N
          (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS z'.1))).id) :
    (z.1 = (cutLRep R hR).2.B.source ↔ z'.1 = (cutLRep S hS).2.B.source) ∧
    (z.1 = v ↔ z'.1 = v') ∧
    (∀ (d : selectedDarts (presentation (cutLRep R hR).2 .left v))
      (e : selectedDarts (presentation (cutLRep S hS).2 .left v')),
      outerSucc_castDart (kmswStage_nextEdge_mono w ha)
        (I.toEquiv (cutLRepDartMap R hR d.1)) =
          J.toEquiv (cutLRepDartMap S hS e.1) →
      (dartTailVertex (cutLRep R hR).2.B.map d.1 = z.1 ↔
        dartTailVertex (cutLRep S hS).2.B.map e.1 = z'.1)) := by
  let P := presentation (cutLRep R hR).2 .left v
  let Q := presentation (cutLRep S hS).2 .left v'
  let f := (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
    cutLRepDartMap R hR
  let g := J.toEquiv ∘ cutLRepDartMap S hS
  let F := fun z => (stageMapVertex w a
    (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR z))).id
  let G := fun z => (stageMapVertex w N
    (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS z))).id
  have hF : Function.Injective F :=
    (image_stage_vertex_injective w a R I).comp (cutLRep_embedding_fields R hR).2.1
  have hG : Function.Injective G :=
    (image_stage_vertex_injective w N S J).comp (cutLRep_embedding_fields S hS).2.1
  let head := fun d : StageDart (kmswStage w N).nextEdge =>
    if d.2 then edgeWest w d.1.val else edgeEast w d.1.val
  have hf : ∀ d, F (dartHeadVertex P.rep.B.map d) = head (f d) := by
    intro d
    dsimp only [F, P]
    rw [image_cutL_head, image_stage_vertex_head]
    rfl
  have hg : ∀ d, G (dartHeadVertex Q.rep.B.map d) = head (g d) := by
    intro d
    dsimp only [G, Q]
    rw [image_cutL_head, image_stage_vertex_head]
    rfl
  have ho : ∀ d e, f d = g e → (P.rep.B.map.tail d ↔ Q.rep.B.map.tail e) := by
    intro d e hde
    rw [(cutLRep_embedding_fields R hR).2.2.2.1,
      (cutLRep_embedding_fields S hS).2.2.2.1,
      image_stage_tail_side w R I, image_stage_tail_side w S J]
    exact Iff.of_eq (congrArg
      (fun d : StageDart (kmswStage w N).nextEdge => d.2 = false) hde)
  have himg : f '' selectedDarts P = g '' selectedDarts Q :=
    cutLRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv'
  change F z.1 = G z'.1 at hz
  refine ⟨⟨image_root_forward P Q f g F G head hF hf hg ho himg z z' hz,
    image_root_forward Q P g f G F head hG hg hf
      (fun e d h => (ho d e h.symm).symm) himg.symm z' z hz.symm⟩, ?_, ?_⟩
  · rw [← hF.eq_iff, ← hG.eq_iff]
    rw [hz, show F v = G v' from hv.trans hv'.symm]
  · intro d e hde
    rw [← hF.eq_iff, ← hG.eq_iff]
    change F (dartTailVertex P.rep.B.map d.1) = F z.1 ↔
      G (dartTailVertex Q.rep.B.map e.1) = G z'.1
    have htail : F (dartTailVertex P.rep.B.map d.1) =
        G (dartTailVertex Q.rep.B.map e.1) := by
      dsimp only [F, G, P, Q]
      rw [image_cutL_tail, image_cutL_tail, image_stage_vertex_tail,
        image_stage_vertex_tail]
      exact congrArg
        (fun c : StageDart (kmswStage w N).nextEdge =>
          if c.2 then edgeEast w c.1.val else edgeWest w c.1.val) hde
    rw [htail, hz]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Matching ancestor vertices preserve root, target and selected-dart incidence. -/
theorem cutRRep_ancestor_marks_stage_iff
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id = (recordVertex w u).id)
    (z : ancestors (presentation (cutRRep R hR).2 .right v))
    (z' : ancestors (presentation (cutRRep S hS).2 .right v'))
    (hz : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z.1))).id =
        (stageMapVertex w N
          (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS z'.1))).id) :
    (z.1 = (cutRRep R hR).2.B.source ↔ z'.1 = (cutRRep S hS).2.B.source) ∧
    (z.1 = v ↔ z'.1 = v') ∧
    (∀ (d : selectedDarts (presentation (cutRRep R hR).2 .right v))
      (e : selectedDarts (presentation (cutRRep S hS).2 .right v')),
      outerSucc_castDart (kmswStage_nextEdge_mono w ha)
        (I.toEquiv (cutRRepDartMap R hR d.1)) =
          J.toEquiv (cutRRepDartMap S hS e.1) →
      (dartTailVertex (cutRRep R hR).2.B.map d.1 = z.1 ↔
        dartTailVertex (cutRRep S hS).2.B.map e.1 = z'.1)) := by
  let P := presentation (cutRRep R hR).2 .right v
  let Q := presentation (cutRRep S hS).2 .right v'
  let f := (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
    cutRRepDartMap R hR
  let g := J.toEquiv ∘ cutRRepDartMap S hS
  let F := fun z => (stageMapVertex w a
    (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z))).id
  let G := fun z => (stageMapVertex w N
    (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS z))).id
  have hF : Function.Injective F :=
    (image_stage_vertex_injective w a R I).comp (cutRRep_embedding_fields R hR).2.1
  have hG : Function.Injective G :=
    (image_stage_vertex_injective w N S J).comp (cutRRep_embedding_fields S hS).2.1
  let head := fun d : StageDart (kmswStage w N).nextEdge =>
    if d.2 then edgeWest w d.1.val else edgeEast w d.1.val
  have hf : ∀ d, F (dartHeadVertex P.rep.B.map d) = head (f d) := by
    intro d
    dsimp only [F, P]
    rw [image_cutR_head, image_stage_vertex_head]
    rfl
  have hg : ∀ d, G (dartHeadVertex Q.rep.B.map d) = head (g d) := by
    intro d
    dsimp only [G, Q]
    rw [image_cutR_head, image_stage_vertex_head]
    rfl
  have ho : ∀ d e, f d = g e → (P.rep.B.map.tail d ↔ Q.rep.B.map.tail e) := by
    intro d e hde
    rw [(cutRRep_embedding_fields R hR).2.2.2.1,
      (cutRRep_embedding_fields S hS).2.2.2.1,
      image_stage_tail_side w R I, image_stage_tail_side w S J]
    exact Iff.of_eq (congrArg
      (fun d : StageDart (kmswStage w N).nextEdge => d.2 = false) hde)
  have himg : f '' selectedDarts P = g '' selectedDarts Q :=
    cutRRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv'
  change F z.1 = G z'.1 at hz
  refine ⟨⟨image_root_forward P Q f g F G head hF hf hg ho himg z z' hz,
    image_root_forward Q P g f G F head hG hg hf
      (fun e d h => (ho d e h.symm).symm) himg.symm z' z hz.symm⟩, ?_, ?_⟩
  · rw [← hF.eq_iff, ← hG.eq_iff]
    rw [hz, show F v = G v' from hv.trans hv'.symm]
  · intro d e hde
    rw [← hF.eq_iff, ← hG.eq_iff]
    change F (dartTailVertex P.rep.B.map d.1) = F z.1 ↔
      G (dartTailVertex Q.rep.B.map e.1) = G z'.1
    have htail : F (dartTailVertex P.rep.B.map d.1) =
        G (dartTailVertex Q.rep.B.map e.1) := by
      dsimp only [F, G, P, Q]
      rw [image_cutR_tail, image_cutR_tail, image_stage_vertex_tail,
        image_stage_vertex_tail]
      exact congrArg
        (fun c : StageDart (kmswStage w N).nextEdge =>
          if c.2 then edgeEast w c.1.val else edgeWest w c.1.val) hde
    rw [htail, hz]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both selected half images agree when the two target records precede the earlier stage. -/
theorem selectedCutSideImagesAgree_stage
    (uL uR : ℕ) (huL : uL ≤ a) (huR : uR ≤ a)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (z : MapVertex (cutRRep R hR).2.B.map)
    (z' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id = (recordVertex w uL).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id = (recordVertex w uL).id)
    (hz : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z))).id = (recordVertex w uR).id)
    (hz' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS z'))).id = (recordVertex w uR).id) :
    SelectedCutSideImagesAgree R hR S hS v v' z z'
      ((outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
        cutLRepDartMap R hR)
      (J.toEquiv ∘ cutLRepDartMap S hS)
      ((outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) ∘
        cutRRepDartMap R hR)
      (J.toEquiv ∘ cutRRepDartMap S hS) := by
  exact ⟨cutLRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg uL huL v v' hv hv',
    cutRRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg uR huR z z' hz hz'⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected left dart carriers are equivalent by their common-stage images. -/
theorem cutLRep_selectedDarts_stage_equiv
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id = (recordVertex w u).id) :
    ∃ e : selectedDarts (presentation (cutLRep R hR).2 .left v) ≃
        selectedDarts (presentation (cutLRep S hS).2 .left v'),
      ∀ d, outerSucc_castDart (kmswStage_nextEdge_mono w ha)
          (I.toEquiv (cutLRepDartMap R hR d.1)) =
        J.toEquiv (cutLRepDartMap S hS (e d).1) := by
  exact image_subtype_equiv _ _
    ((image_stage_injective w ha R I).comp (cutLRep_embedding_fields R hR).1)
    (J.toEquiv.injective.comp (cutLRep_embedding_fields S hS).1) _ _
    (cutLRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv')

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Surviving left seam marks have identical indices and common-stage images. -/
theorem cutLRep_selected_seam_stage_image_eq
    (u s : ℕ) (hu : u ≤ a) (hs : s + 1 ≤ ℓ) (hs' : s + 1 ≤ ℓ')
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (hb : boundaryTarget (cutLRep R hR).2.B .left s = some v)
    (hb' : boundaryTarget (cutLRep S hS).2.B .left s = some v')
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id = (recordVertex w u).id) :
    ∀ (i : ℕ) (z : StageDart (kmswStage w N).nextEdge),
      (∃ d : selectedDarts (presentation (cutLRep R hR).2 .left v),
      (boundaryDarts (cutLRep R hR).2.B .right)[i]? = some d.1 ∧
        outerSucc_castDart (kmswStage_nextEdge_mono w ha)
          (I.toEquiv (cutLRepDartMap R hR d.1)) = z) ↔
      (∃ e : selectedDarts (presentation (cutLRep S hS).2 .left v'),
        (boundaryDarts (cutLRep S hS).2.B .right)[i]? = some e.1 ∧
          J.toEquiv (cutLRepDartMap S hS e.1) = z) := by
  obtain ⟨c, hc, hci⟩ := seam_selectedDart_initial_segment
    (cutLRep R hR).2 .left s v hs hb
  obtain ⟨c', _, hci'⟩ := seam_selectedDart_initial_segment
    (cutLRep S hS).2 .left s v' hs' hb'
  have hcm : c < m := by
    simpa only [oppositeSide, boundaryDarts,
      (cutLRep R hR).2.B.rightPath.darts_length] using hc
  exact image_selected_list_prefix _ _
    ((image_stage_injective w ha R I).comp (cutLRep_embedding_fields R hR).1)
    (J.toEquiv.injective.comp (cutLRep_embedding_fields S hS).1) _ _
    (cutLRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv') _ _ m c c' hcm hci hci'
    (image_boundary_prefix _ _ _ _ _ _ _ _
      (cutLRep_boundaryDarts_map R hR).2 (cutLRep_boundaryDarts_map S hS).2 m hP.2.1)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected right dart carriers are equivalent by their common-stage images. -/
theorem cutRRep_selectedDarts_stage_equiv
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id = (recordVertex w u).id) :
    ∃ e : selectedDarts (presentation (cutRRep R hR).2 .right v) ≃
        selectedDarts (presentation (cutRRep S hS).2 .right v'),
      ∀ d, outerSucc_castDart (kmswStage_nextEdge_mono w ha)
          (I.toEquiv (cutRRepDartMap R hR d.1)) =
        J.toEquiv (cutRRepDartMap S hS (e d).1) := by
  exact image_subtype_equiv _ _
    ((image_stage_injective w ha R I).comp (cutRRep_embedding_fields R hR).1)
    (J.toEquiv.injective.comp (cutRRep_embedding_fields S hS).1) _ _
    (cutRRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv')

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Surviving right seam marks have identical indices and common-stage images. -/
theorem cutRRep_selected_seam_stage_image_eq
    (u s : ℕ) (hu : u ≤ a) (hs : s + 1 ≤ r) (hs' : s + 1 ≤ r')
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (hb : boundaryTarget (cutRRep R hR).2.B .right s = some v)
    (hb' : boundaryTarget (cutRRep S hS).2.B .right s = some v')
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id = (recordVertex w u).id) :
    ∀ (i : ℕ) (z : StageDart (kmswStage w N).nextEdge),
      (∃ d : selectedDarts (presentation (cutRRep R hR).2 .right v),
      (boundaryDarts (cutRRep R hR).2.B .left)[i]? = some d.1 ∧
        outerSucc_castDart (kmswStage_nextEdge_mono w ha)
          (I.toEquiv (cutRRepDartMap R hR d.1)) = z) ↔
      (∃ e : selectedDarts (presentation (cutRRep S hS).2 .right v'),
        (boundaryDarts (cutRRep S hS).2.B .left)[i]? = some e.1 ∧
          J.toEquiv (cutRRepDartMap S hS e.1) = z) := by
  obtain ⟨c, hc, hci⟩ := seam_selectedDart_initial_segment
    (cutRRep R hR).2 .right s v hs hb
  obtain ⟨c', _, hci'⟩ := seam_selectedDart_initial_segment
    (cutRRep S hS).2 .right s v' hs' hb'
  have hcm : c < m := by
    simpa only [oppositeSide, boundaryDarts,
      (cutRRep R hR).2.B.leftPath.darts_length] using hc
  exact image_selected_list_prefix _ _
    ((image_stage_injective w ha R I).comp (cutRRep_embedding_fields R hR).1)
    (J.toEquiv.injective.comp (cutRRep_embedding_fields S hS).1) _ _
    (cutRRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv') _ _ m c c' hcm hci hci'
    (image_boundary_prefix _ _ _ _ _ _ _ _
      (cutRRep_boundaryDarts_map R hR).2 (cutRRep_boundaryDarts_map S hS).2 m hP.2.1)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Matching selected left darts have the same induced first-return rotation relation. -/
theorem cutLRep_truncation_rotation_stage_iff
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id = (recordVertex w u).id)
    (d e : selectedDarts (presentation (cutLRep R hR).2 .left v))
    (d' e' : selectedDarts (presentation (cutLRep S hS).2 .left v'))
    (hd : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutLRepDartMap R hR d.1)) =
        J.toEquiv (cutLRepDartMap S hS d'.1))
    (he : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutLRepDartMap R hR e.1)) =
        J.toEquiv (cutLRepDartMap S hS e'.1)) :
    truncationRelation (presentation (cutLRep R hR).2 .left v)
        .rotation (.inr d) (.inr e) ↔
      truncationRelation (presentation (cutLRep S hS).2 .left v')
        .rotation (.inr d') (.inr e') := by
  let f := outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘
    I.toEquiv ∘ cutLRepDartMap R hR
  let g := J.toEquiv ∘ cutLRepDartMap S hS
  have hrot := cutLRep_truncation_rotation_later_stage R hR I ha v d e
  have hrot' := cutLRep_truncation_rotation_later_stage S hS J (le_refl N) v' d' e'
  change _ ↔ (∃ k : ℕ, 0 < k ∧
    (stageRot w N : _ → _)^[k] (g d'.1) = g e'.1 ∧
    ∀ j : ℕ, 0 < j → j < k → (stageRot w N : _ → _)^[j] (g d'.1) ∉
      g '' selectedDarts (presentation (cutLRep S hS).2 .left v')) at hrot'
  have himg : f '' selectedDarts (presentation (cutLRep R hR).2 .left v) =
      g '' selectedDarts (presentation (cutLRep S hS).2 .left v') :=
    cutLRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv'
  refine hrot.trans (Iff.trans ?_ hrot'.symm)
  change (∃ k : ℕ, 0 < k ∧ (stageRot w N : _ → _)^[k] (f d.1) = f e.1 ∧
    ∀ j : ℕ, 0 < j → j < k → (stageRot w N : _ → _)^[j] (f d.1) ∉
      f '' selectedDarts (presentation (cutLRep R hR).2 .left v)) ↔ _
  change f d.1 = g d'.1 at hd
  change f e.1 = g e'.1 at he
  rw [hd, he, himg]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Matching selected right darts have the same induced first-return rotation relation. -/
theorem cutRRep_truncation_rotation_stage_iff
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id = (recordVertex w u).id)
    (d e : selectedDarts (presentation (cutRRep R hR).2 .right v))
    (d' e' : selectedDarts (presentation (cutRRep S hS).2 .right v'))
    (hd : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutRRepDartMap R hR d.1)) =
        J.toEquiv (cutRRepDartMap S hS d'.1))
    (he : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutRRepDartMap R hR e.1)) =
        J.toEquiv (cutRRepDartMap S hS e'.1)) :
    truncationRelation (presentation (cutRRep R hR).2 .right v)
        .rotation (.inr d) (.inr e) ↔
      truncationRelation (presentation (cutRRep S hS).2 .right v')
        .rotation (.inr d') (.inr e') := by
  let f := outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘
    I.toEquiv ∘ cutRRepDartMap R hR
  let g := J.toEquiv ∘ cutRRepDartMap S hS
  have hrot := cutRRep_truncation_rotation_later_stage R hR I ha v d e
  have hrot' := cutRRep_truncation_rotation_later_stage S hS J (le_refl N) v' d' e'
  change _ ↔ (∃ k : ℕ, 0 < k ∧
    (stageRot w N : _ → _)^[k] (g d'.1) = g e'.1 ∧
    ∀ j : ℕ, 0 < j → j < k → (stageRot w N : _ → _)^[j] (g d'.1) ∉
      g '' selectedDarts (presentation (cutRRep S hS).2 .right v')) at hrot'
  have himg : f '' selectedDarts (presentation (cutRRep R hR).2 .right v) =
      g '' selectedDarts (presentation (cutRRep S hS).2 .right v') :=
    cutRRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv'
  refine hrot.trans (Iff.trans ?_ hrot'.symm)
  change (∃ k : ℕ, 0 < k ∧ (stageRot w N : _ → _)^[k] (f d.1) = f e.1 ∧
    ∀ j : ℕ, 0 < j → j < k → (stageRot w N : _ → _)^[j] (f d.1) ∉
      f '' selectedDarts (presentation (cutRRep R hR).2 .right v)) ↔ _
  change f d.1 = g d'.1 at hd
  change f e.1 = g e'.1 at he
  rw [hd, he, himg]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Right retained faces correspond in both directions across the common stage. -/
theorem cutRRep_retainedFace_stage_iff
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id = (recordVertex w u).id)
    (d : Fin (cutRRep R hR).2.dartCount)
    (e : Fin (cutRRep S hS).2.dartCount)
    (hde : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutRRepDartMap R hR d)) =
        J.toEquiv (cutRRepDartMap S hS e)) :
    retainedFace (presentation (cutRRep R hR).2 .right v) d ↔
      retainedFace (presentation (cutRRep S hS).2 .right v') e := by
  apply cutRRep_retainedFace_iff_of_image_eq_of_nonouter R hR S hS v v'
    (kmswMap w N).faceSucc
    (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv
    (image_stage_injective w ha R I) J.toEquiv.injective
    (cutRRep_selectedDarts_stage_image_eq w ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hv hv') d e hde
    (cutRRep_isOuter_stage_iff w ha R hR S hS I J fv gv hP d e hde)
  · intro hd
    exact selectedStage_faceOrbit_compat w ha R I (cutRRepDartMap R hR d)
      (image_cutR_nonouter R hR d hd)
  · intro _
    exact selectedStage_iso_faceOrbit_compat w S J (cutRRepDartMap S hS e)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Right retained-face successor relations agree for matching selected darts. -/
theorem cutRRep_truncation_faceNext_stage_iff
    (u : ℕ) (hu : u ≤ a)
    (v : MapVertex (cutRRep R hR).2.B.map)
    (v' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w a
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id = (recordVertex w u).id)
    (hv' : (stageMapVertex w N
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id = (recordVertex w u).id)
    (d e : selectedDarts (presentation (cutRRep R hR).2 .right v))
    (d' e' : selectedDarts (presentation (cutRRep S hS).2 .right v'))
    (hd : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutRRepDartMap R hR d.1)) =
        J.toEquiv (cutRRepDartMap S hS d'.1))
    (he : outerSucc_castDart (kmswStage_nextEdge_mono w ha)
      (I.toEquiv (cutRRepDartMap R hR e.1)) =
        J.toEquiv (cutRRepDartMap S hS e'.1)) :
    truncationRelation (presentation (cutRRep R hR).2 .right v)
        .faceNext (.inr d) (.inr e) ↔
      truncationRelation (presentation (cutRRep S hS).2 .right v')
        .faceNext (.inr d') (.inr e') := by
  let τ := selectedStageDartTransport w ha R S I J
  have hτd : τ (cutRRepDartMap R hR d.1) = cutRRepDartMap S hS d'.1 := by
    apply J.toEquiv.injective
    exact (J.toEquiv.apply_symm_apply _).trans hd
  have hτe : τ (cutRRepDartMap R hR e.1) = cutRRepDartMap S hS e'.1 := by
    apply J.toEquiv.injective
    exact (J.toEquiv.apply_symm_apply _).trans he
  have hτinj : Function.Injective τ :=
    J.toEquiv.symm.injective.comp (image_stage_injective w ha R I)
  have hret := cutRRep_retainedFace_stage_iff w ha R hR S hS I J fv gv hP
    hL hRneg u hu v v' hv hv' d.1 d'.1 hd
  have hnext (hf : retainedFace (presentation (cutRRep R hR).2 .right v) d.1) :
      τ (cutRRepDartMap R hR
          ((cutRRep R hR).2.B.map.toCombinatorialMap.faceSucc d.1)) =
        cutRRepDartMap S hS
          ((cutRRep S hS).2.B.map.toCombinatorialMap.faceSucc d'.1) := by
    have hc := selectedStageDartTransport_faceSucc w ha R S I J
      (cutRRepDartMap R hR d.1) (image_cutR_nonouter R hR d.1 hf.1)
    change τ (R.B.map.toCombinatorialMap.faceSucc (cutRRepDartMap R hR d.1)) =
      S.B.map.toCombinatorialMap.faceSucc (τ (cutRRepDartMap R hR d.1)) at hc
    rw [cutRRep_retainedFace_faceSucc_map R hR v d.1 hf, hc, hτd,
      cutRRep_retainedFace_faceSucc_map S hS v' d'.1 (hret.mp hf)]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · rintro ⟨hf, hde⟩
    refine ⟨hret.mp hf, (cutRRep_embedding_fields S hS).1 ?_⟩
    exact (hnext hf).symm.trans
      ((congrArg (τ ∘ cutRRepDartMap R hR) hde).trans hτe)
  · rintro ⟨hf, hde⟩
    have hf' := hret.mpr hf
    refine ⟨hf', ((hτinj.comp (cutRRep_embedding_fields R hR).1) ?_)⟩
    exact (hnext hf').trans
      ((congrArg (cutRRepDartMap S hS) hde).trans hτe.symm)

end StageImages

private theorem image_boundary_marked {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ) (v : MapVertex R.B.map)
    (hv : boundaryTarget R.B a s = some v) {A : Type*} (f : Fin R.dartCount → A)
    (b : ℕ → A) (hp : ∀ i < s, ((boundaryDarts R.B a)[i]?).map f = some (b i))
    (i : ℕ) (z : A) :
    (∃ d : selectedDarts (presentation R a v),
      (boundaryDarts R.B a)[i]? = some d.1 ∧ f d.1 = z) ↔
        i < s ∧ z = b i := by
  constructor
  · rintro ⟨d, hd, hz⟩
    have hi := (boundary_selectedDart_index_iff R a s i v d.1 hv hd).mp d.2
    have hh := hp i hi
    rw [hd, Option.map_some] at hh
    exact ⟨hi, hz.symm.trans (Option.some.inj hh)⟩
  · rintro ⟨hi, hz⟩
    obtain ⟨d, hd⟩ := (boundary_selectedDart_exists_iff R a s i v hv).mpr hi
    have hh := hp i hi
    rw [hd, Option.map_some] at hh
    exact ⟨d, hd, (Option.some.inj hh).trans hz.symm⟩

open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3 in
private theorem image_representatives_boundary_targets
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1)))
      (vL : MapVertex (cutLRep R hR).2.B.map)
      (vR : MapVertex (cutRRep R hR).2.B.map),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      boundaryTarget (cutLRep R hR).2.B .left s = some vL ∧
      boundaryTarget (cutRRep R hR).2.B .right s = some vR ∧
      (stageMapVertex w (t - 1)
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR vL))).id =
          edgeWest w (kmswLeftBoundaryEdge w s) ∧
      (∀ (i : ℕ) (z : ℕ × Bool),
        (∃ e : selectedDarts (presentation (cutLRep R hR).2 .left vL),
          (boundaryDarts (cutLRep R hR).2.B .left)[i]? = some e.1 ∧
            ((I.toEquiv (cutLRepDartMap R hR e.1)).1.val,
              (I.toEquiv (cutLRepDartMap R hR e.1)).2) = z) ↔
          i < s ∧ z = (kmswLeftBoundaryEdge w i, false)) ∧
      (∀ (i : ℕ) (z : ℕ × Bool),
        (∃ e : selectedDarts (presentation (cutRRep R hR).2 .right vR),
          (boundaryDarts (cutRRep R hR).2.B .right)[i]? = some e.1 ∧
            ((I.toEquiv (cutRRepDartMap R hR e.1)).1.val,
              (I.toEquiv (cutRRepDartMap R hR e.1)).2) = z) ↔
          i < s ∧ z = (kmswRightBoundaryEdge w i, false)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, R, hR, I, hℓ, hr, hb, ht, hc⟩ :=
    selectedCutPastCuts_representatives_record_stageIso x T hT q k s hk
  obtain ⟨bL, hbL, hidL, _⟩ := ht .left
  obtain ⟨bR, hbR, _, _⟩ := ht .right
  have hL := cutLRep_boundaryTarget_map R hR s
  have hR' := cutRRep_boundaryTarget_map R hR s
  rw [hbL] at hL
  rw [hbR] at hR'
  obtain ⟨vL, hvL, heL⟩ := Option.map_eq_some_iff.mp hL
  obtain ⟨vR, hvR, _⟩ := Option.map_eq_some_iff.mp hR'
  refine ⟨ℓ, d, R, hR, I, vL, vR, hℓ, hr, hvL, hvR, ?_, ?_, ?_, hc⟩
  · rw [heL]
    exact hidL
  · refine image_boundary_marked _ .left s vL hvL
      (fun e => ((I.toEquiv (cutLRepDartMap R hR e)).1.val,
        (I.toEquiv (cutLRepDartMap R hR e)).2))
      (fun i => (kmswLeftBoundaryEdge (boltzmannKMSWStream (pathCode q.1)) i, false)) ?_
    intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q .left k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb .left)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (cutLRep_boundaryDarts_map R hR).1
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    exact hm.trans hs
  · refine image_boundary_marked _ .right s vR hvR
      (fun e => ((I.toEquiv (cutRRepDartMap R hR e)).1.val,
        (I.toEquiv (cutRRepDartMap R hR e)).2))
      (fun i => (kmswRightBoundaryEdge (boltzmannKMSWStream (pathCode q.1)) i, false)) ?_
    intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q .right k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb .right)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (cutRRep_boundaryDarts_map R hR).1
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    exact hm.trans hs

open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3 in
private theorem image_representatives_both_boundary_targets
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    let r := (-(q.1 t).2).toNat
    ∃ (ℓ d : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = d)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1)))
      (vL : MapVertex (cutLRep R hR).2.B.map)
      (vR : MapVertex (cutRRep R hR).2.B.map),
      s + 1 ≤ ℓ ∧ s + 1 ≤ r ∧
      boundaryTarget (cutLRep R hR).2.B .left s = some vL ∧
      boundaryTarget (cutRRep R hR).2.B .right s = some vR ∧
      (stageMapVertex w (t - 1)
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR vL))).id =
          edgeWest w (kmswLeftBoundaryEdge w s) ∧
      (stageMapVertex w (t - 1)
        (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR vR))).id =
          edgeWest w (kmswRightBoundaryEdge w s) ∧
      (∀ (i : ℕ) (z : ℕ × Bool),
        (∃ e : selectedDarts (presentation (cutLRep R hR).2 .left vL),
          (boundaryDarts (cutLRep R hR).2.B .left)[i]? = some e.1 ∧
            ((I.toEquiv (cutLRepDartMap R hR e.1)).1.val,
              (I.toEquiv (cutLRepDartMap R hR e.1)).2) = z) ↔
          i < s ∧ z = (kmswLeftBoundaryEdge w i, false)) ∧
      (∀ (i : ℕ) (z : ℕ × Bool),
        (∃ e : selectedDarts (presentation (cutRRep R hR).2 .right vR),
          (boundaryDarts (cutRRep R hR).2.B .right)[i]? = some e.1 ∧
            ((I.toEquiv (cutRRepDartMap R hR e.1)).1.val,
              (I.toEquiv (cutRRepDartMap R hR e.1)).2) = z) ↔
          i < s ∧ z = (kmswRightBoundaryEdge w i, false)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, R, hR, I, hℓ, hr, hb, ht, hc⟩ :=
    selectedCutPastCuts_representatives_record_stageIso x T hT q k s hk
  obtain ⟨bL, hbL, hidL, _⟩ := ht .left
  obtain ⟨bR, hbR, hidR, _⟩ := ht .right
  have hL := cutLRep_boundaryTarget_map R hR s
  have hR' := cutRRep_boundaryTarget_map R hR s
  rw [hbL] at hL
  rw [hbR] at hR'
  obtain ⟨vL, hvL, heL⟩ := Option.map_eq_some_iff.mp hL
  obtain ⟨vR, hvR, heR⟩ := Option.map_eq_some_iff.mp hR'
  refine ⟨ℓ, d, R, hR, I, vL, vR, hℓ, hr, hvL, hvR, ?_, ?_, ?_, ?_, hc⟩
  · rw [heL]
    exact hidL
  · rw [heR]
    exact hidR
  · refine image_boundary_marked _ .left s vL hvL
      (fun e => ((I.toEquiv (cutLRepDartMap R hR e)).1.val,
        (I.toEquiv (cutLRepDartMap R hR e)).2))
      (fun i => (kmswLeftBoundaryEdge (boltzmannKMSWStream (pathCode q.1)) i, false)) ?_
    intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q .left k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb .left)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (cutLRep_boundaryDarts_map R hR).1
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    exact hm.trans hs
  · refine image_boundary_marked _ .right s vR hvR
      (fun e => ((I.toEquiv (cutRRepDartMap R hR e)).1.val,
        (I.toEquiv (cutRRepDartMap R hR e)).2))
      (fun i => (kmswRightBoundaryEdge (boltzmannKMSWStream (pathCode q.1)) i, false)) ?_
    intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q .right k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb .right)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (cutRRep_boundaryDarts_map R hR).1
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    exact hm.trans hs

section SelectedCuts
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
variable (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (s k K : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (hK : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (K + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2))

local notation "w₀" => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "t₀" => ENat.toNat (selectedCutTime T (k + 1) (Subtype.val q)) - 1
local notation "N₀" => ENat.toNat (selectedCutTime T (K + 1) (Subtype.val q)) - 1

include hk hK

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual good-cut stages have equal selected half images under the common-prefix input.
The target identifications are the representative data provided by
`selectedCutPastCuts_representatives_half_ancestors`; no ancestry premise is added. -/
theorem selectedCutSideImagesAgree_selectedCuts
    {ℓ r n m ℓ' r' n' m' : ℕ} {β : Type*} (ha : t₀ ≤ N₀)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv) J.toEquiv fv gv)
    (v : MapVertex (cutLRep R hR).2.B.map)
    (v' : MapVertex (cutLRep S hS).2.B.map)
    (z : MapVertex (cutRRep R hR).2.B.map)
    (z' : MapVertex (cutRRep S hS).2.B.map)
    (hv : (stageMapVertex w₀ t₀
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
        edgeWest w₀ (kmswLeftBoundaryEdge w₀ s))
    (hv' : (stageMapVertex w₀ N₀
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id =
        edgeWest w₀ (kmswLeftBoundaryEdge w₀ s))
    (hz : (stageMapVertex w₀ t₀
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z))).id =
        edgeWest w₀ (kmswRightBoundaryEdge w₀ s))
    (hz' : (stageMapVertex w₀ N₀
      (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS z'))).id =
        edgeWest w₀ (kmswRightBoundaryEdge w₀ s)) :
    SelectedCutSideImagesAgree R hR S hS v v' z z'
      ((outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv) ∘
        cutLRepDartMap R hR)
      (J.toEquiv ∘ cutLRepDartMap S hS)
      ((outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv) ∘
        cutRRepDartMap R hR)
      (J.toEquiv ∘ cutRRepDartMap S hS) := by
  have hbL := selectedCut_boundary_target_record x T hT q .left k s hk
  have hbR := selectedCut_boundary_target_record x T hT q .right k s hk
  have hBL := selectedCut_boundary_target_record x T hT q .left K s hK
  have hBR := selectedCut_boundary_target_record x T hT q .right K s hK
  obtain ⟨_, _, _, _, _, _, _, hRneg, hL, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let uL := natSelect (fun m => ∀ j, m < j → L w₀ m + 1 ≤ L w₀ j) s
  let uR := natSelect (fun m => ∀ j, j < m → KMSW.R w₀ m < KMSW.R w₀ j) s
  have huL : uL ≤ t₀ := by
    have hh : uL < (selectedCutTime T (k + 1) q.1).toNat := hbL.1
    omega
  have huR : uR ≤ t₀ := by
    have hh : uR < (selectedCutTime T (k + 1) q.1).toNat := hbR.1
    omega
  apply selectedCutSideImagesAgree_stage w₀ ha R hR S hS I J fv gv hP hL hRneg
    uL uR huL huR v v' z z'
  · exact hv.trans (congrArg PresentVertex.id hbL.2).symm
  · exact hv'.trans (congrArg PresentVertex.id hBL.2).symm
  · exact hz.trans (congrArg PresentVertex.id hbR.2).symm
  · exact hz'.trans (congrArg PresentVertex.id hBR.2).symm


/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual good-cut representatives can be chosen so that matching selected
left darts have the same indexed original boundary marks. The proof uses only
indices below `s` and permanent edge IDs, with no general left-arc transport. -/
theorem selectedCutPastCuts_representatives_left_boundary_stage_transport
    (ha : t₀ ≤ N₀) :
    ∃ (ℓ d ℓ' d' : ℕ)
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
      (v : MapVertex (cutLRep R hR).2.B.map)
      (v' : MapVertex (cutLRep S hS).2.B.map),
      boundaryTarget (cutLRep R hR).2.B .left s = some v ∧
      boundaryTarget (cutLRep S hS).2.B .left s = some v' ∧
      (stageMapVertex w₀ t₀
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (stageMapVertex w₀ N₀
        (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
        (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
        outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
            (I.toEquiv (cutLRepDartMap R hR b.1)) =
          J.toEquiv (cutLRepDartMap S hS c.1) →
        ∀ i : ℕ, ((boundaryDarts (cutLRep R hR).2.B .left)[i]? = some b.1 ↔
          (boundaryDarts (cutLRep S hS).2.B .left)[i]? = some c.1)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, R, hR, I, v, _, _, _, hv, _, hid, hb, _, hc⟩ :=
    image_representatives_boundary_targets x T hT q k s hk
  obtain ⟨ℓ', d', S, hS, J, v', _, _, _, hv', _, hid', hb', _, hc'⟩ :=
    image_representatives_boundary_targets x T hT q K s hK
  refine ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', ?_, hc, hc'⟩
  intro b c hbc
  have hid : ((I.toEquiv (cutLRepDartMap R hR b.1)).1.val,
      (I.toEquiv (cutLRepDartMap R hR b.1)).2) =
      ((J.toEquiv (cutLRepDartMap S hS c.1)).1.val,
        (J.toEquiv (cutLRepDartMap S hS c.1)).2) :=
    congrArg (fun z : StageDart (kmswStage w₀ N₀).nextEdge => (z.1.val, z.2)) hbc
  intro i
  constructor
  · intro hget
    have hmark := (hb i _).mp ⟨b, hget, rfl⟩
    obtain ⟨e, he, heid⟩ := (hb' i _).mpr ⟨hmark.1, hid.symm.trans hmark.2⟩
    have heq : e.1 = c.1 := by
      apply (cutLRep_embedding_fields S hS).1
      apply J.toEquiv.injective
      apply Prod.ext
      · exact Fin.ext (congrArg (fun z : ℕ × Bool => z.1) heid)
      · exact congrArg (fun z : ℕ × Bool => z.2) heid
    rw [heq] at he
    exact he
  · intro hget
    have hmark := (hb' i _).mp ⟨c, hget, rfl⟩
    obtain ⟨e, he, heid⟩ := (hb i _).mpr ⟨hmark.1, hid.trans hmark.2⟩
    have heq : e.1 = b.1 := by
      apply (cutLRep_embedding_fields R hR).1
      apply I.toEquiv.injective
      apply Prod.ext
      · exact Fin.ext (congrArg (fun z : ℕ × Bool => z.1) heid)
      · exact congrArg (fun z : ℕ × Bool => z.2) heid
    rw [heq] at he
    exact he


/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Matching selected darts of the actual good-cut left halves have equivalent
outer-face membership, using their permanent original boundary marks. -/
theorem selectedCutPastCuts_representatives_left_outer_stage_iff
    (ha : t₀ ≤ N₀) {β : Type*} :
    ∃ (ℓ d ℓ' d' : ℕ)
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
      (v : MapVertex (cutLRep R hR).2.B.map)
      (v' : MapVertex (cutLRep S hS).2.B.map),
      boundaryTarget (cutLRep R hR).2.B .left s = some v ∧
      boundaryTarget (cutLRep S hS).2.B .left s = some v' ∧
      (stageMapVertex w₀ t₀
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (stageMapVertex w₀ N₀
        (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
        (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
        outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
            (I.toEquiv (cutLRepDartMap R hR b.1)) =
          J.toEquiv (cutLRepDartMap S hS c.1) →
        ∀ i : ℕ, ((boundaryDarts (cutLRep R hR).2.B .left)[i]? = some b.1 ↔
          (boundaryDarts (cutLRep S hS).2.B .left)[i]? = some c.1)) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        ∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
          (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
          outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
              (I.toEquiv (cutLRepDartMap R hR b.1)) =
            J.toEquiv (cutLRepDartMap S hS c.1) →
          ((cutLRep R hR).2.B.map.IsOuter b.1 ↔
            (cutLRep S hS).2.B.map.IsOuter c.1)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', hb, hc, hc'⟩ :=
    selectedCutPastCuts_representatives_left_boundary_stage_transport x T hT q s k K
      hk hK ha
  refine ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', hb, ?_, hc, hc'⟩
  intro fv gv hP b c hbc
  constructor
  · intro ho
    rcases (isOuter_iff_mem_left_or_reverse_right_boundary
      (cutLRep R hR).2.B b.1).mp ho with hl | ⟨z, hz, hbz⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hl
      have hget : (boundaryDarts (cutLRep R hR).2.B .left)[i]? = some b.1 :=
        (List.getElem?_eq_getElem i.isLt).trans (congrArg some hi)
      have hget' := (hb b c hbc i).mp hget
      exact (isOuter_iff_mem_left_or_reverse_right_boundary
        (cutLRep S hS).2.B c.1).mpr (Or.inl (List.mem_of_getElem? hget'))
    · let τ := selectedStageDartTransport w₀ ha R S I J
      have hτ : τ (cutLRepDartMap R hR b.1) = cutLRepDartMap S hS c.1 := by
        apply J.toEquiv.injective
        exact (J.toEquiv.apply_symm_apply _).trans hbc
      have hzpath : cutLRepDartMap R hR z ∈
          (selectedGeodesicOfLen R.B x hR).darts := by
        rw [← (cutLRep_boundaryDarts_map R hR).2]
        exact List.mem_map.mpr ⟨z, hz, rfl⟩
      have hzpath' := selectedStageDartTransport_pathDart w₀ ha R hR S hS I J
        fv gv hP (cutLRepDartMap R hR z) hzpath
      apply (image_cutL_outer S hS c.1).mpr
      refine Or.inr ⟨τ (cutLRepDartMap R hR z), hzpath', ?_⟩
      calc
        cutLRepDartMap S hS c.1 = τ (cutLRepDartMap R hR b.1) := hτ.symm
        _ = τ (R.B.map.edgeInv (cutLRepDartMap R hR z)) :=
          congrArg τ ((congrArg (cutLRepDartMap R hR) hbz).trans
            ((cutLRep_embedding_fields R hR).2.2.1 z))
        _ = S.B.map.edgeInv (τ (cutLRepDartMap R hR z)) :=
          selectedStageDartTransport_edgeInv w₀ ha R S I J _
  · exact cutLRep_isOuter_stage_reflect w₀ ha R hR S hS I J fv gv hP b.1 c.1 hbc


/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual good-cut left representatives can be chosen with equivalent
retained-face predicates on matching selected darts. -/
theorem selectedCutPastCuts_representatives_left_retainedFace_stage_iff
    (ha : t₀ ≤ N₀) {β : Type*} :
    ∃ (ℓ d ℓ' d' : ℕ)
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
      (v : MapVertex (cutLRep R hR).2.B.map)
      (v' : MapVertex (cutLRep S hS).2.B.map),
      boundaryTarget (cutLRep R hR).2.B .left s = some v ∧
      boundaryTarget (cutLRep S hS).2.B .left s = some v' ∧
      (stageMapVertex w₀ t₀
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (stageMapVertex w₀ N₀
        (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
        (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
        outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
            (I.toEquiv (cutLRepDartMap R hR b.1)) =
          J.toEquiv (cutLRepDartMap S hS c.1) →
        ∀ i : ℕ, ((boundaryDarts (cutLRep R hR).2.B .left)[i]? = some b.1 ↔
          (boundaryDarts (cutLRep S hS).2.B .left)[i]? = some c.1)) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        ∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
          (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
          outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
              (I.toEquiv (cutLRepDartMap R hR b.1)) =
            J.toEquiv (cutLRepDartMap S hS c.1) →
          ((cutLRep R hR).2.B.map.IsOuter b.1 ↔
            (cutLRep S hS).2.B.map.IsOuter c.1)) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        ∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
          (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
          outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
              (I.toEquiv (cutLRepDartMap R hR b.1)) =
            J.toEquiv (cutLRepDartMap S hS c.1) →
          (retainedFace (presentation (cutLRep R hR).2 .left v) b.1 ↔
            retainedFace (presentation (cutLRep S hS).2 .left v') c.1)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', hboundary, ho, hc, hc'⟩ :=
    selectedCutPastCuts_representatives_left_outer_stage_iff x T hT q s k K hk hK ha (β := β)
  refine ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', hboundary, ho, ?_, hc, hc'⟩
  intro fv gv hP b c hbc
  obtain ⟨_, _, _, _, _, _, _, hRneg, hL, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let u := natSelect (fun m => ∀ j, m < j → L w₀ m + 1 ≤ L w₀ j) s
  have hb := selectedCut_boundary_target_record x T hT q .left k s hk
  have hb' := selectedCut_boundary_target_record x T hT q .left K s hK
  have hu : u ≤ t₀ := by
    have hh : u < (selectedCutTime T (k + 1) q.1).toNat := hb.1
    omega
  have hvid : (stageMapVertex w₀ t₀
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
      (recordVertex w₀ u).id := hid.trans (congrArg PresentVertex.id hb.2).symm
  have hvid' : (stageMapVertex w₀ N₀
      (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id =
      (recordVertex w₀ u).id := hid'.trans (congrArg PresentVertex.id hb'.2).symm
  apply cutLRep_retainedFace_iff_of_image_eq_of_nonouter R hR S hS v v'
    (kmswMap w₀ N₀).faceSucc
    (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv) J.toEquiv
    (image_stage_injective w₀ ha R I) J.toEquiv.injective
    (cutLRep_selectedDarts_stage_image_eq w₀ ha R hR S hS I J fv gv hP
      hL hRneg u hu v v' hvid hvid') b.1 c.1 hbc (ho fv gv hP b c hbc)
  · intro hd
    exact selectedStage_faceOrbit_compat w₀ ha R I (cutLRepDartMap R hR b.1)
      (image_cutL_nonouter R hR b.1 hd)
  · intro _
    exact selectedStage_iso_faceOrbit_compat w₀ S J (cutLRepDartMap S hS c.1)


/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Matching selected darts in the actual good-cut left representatives have
identical retained-face successor relations. -/
theorem selectedCutPastCuts_representatives_left_faceNext_stage_iff
    (ha : t₀ ≤ N₀) {β : Type*} :
    ∃ (ℓ d ℓ' d' : ℕ)
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
      (v : MapVertex (cutLRep R hR).2.B.map)
      (v' : MapVertex (cutLRep S hS).2.B.map),
      boundaryTarget (cutLRep R hR).2.B .left s = some v ∧
      boundaryTarget (cutLRep S hS).2.B .left s = some v' ∧
      (stageMapVertex w₀ t₀
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (stageMapVertex w₀ N₀
        (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
        (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
        outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
            (I.toEquiv (cutLRepDartMap R hR b.1)) =
          J.toEquiv (cutLRepDartMap S hS c.1) →
        ∀ i : ℕ, ((boundaryDarts (cutLRep R hR).2.B .left)[i]? = some b.1 ↔
          (boundaryDarts (cutLRep S hS).2.B .left)[i]? = some c.1)) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        ∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
          (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
          outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
              (I.toEquiv (cutLRepDartMap R hR b.1)) =
            J.toEquiv (cutLRepDartMap S hS c.1) →
          ((cutLRep R hR).2.B.map.IsOuter b.1 ↔
            (cutLRep S hS).2.B.map.IsOuter c.1)) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        ∀ (b : selectedDarts (presentation (cutLRep R hR).2 .left v))
          (c : selectedDarts (presentation (cutLRep S hS).2 .left v')),
          outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
              (I.toEquiv (cutLRepDartMap R hR b.1)) =
            J.toEquiv (cutLRepDartMap S hS c.1) →
          (retainedFace (presentation (cutLRep R hR).2 .left v) b.1 ↔
            retainedFace (presentation (cutLRep S hS).2 .left v') c.1)) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        ∀ (d e : selectedDarts (presentation (cutLRep R hR).2 .left v))
          (d' e' : selectedDarts (presentation (cutLRep S hS).2 .left v')),
          outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
              (I.toEquiv (cutLRepDartMap R hR d.1)) =
            J.toEquiv (cutLRepDartMap S hS d'.1) →
          outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha)
              (I.toEquiv (cutLRepDartMap R hR e.1)) =
            J.toEquiv (cutLRepDartMap S hS e'.1) →
          (truncationRelation (presentation (cutLRep R hR).2 .left v)
              .faceNext (.inr d) (.inr e) ↔
            truncationRelation (presentation (cutLRep S hS).2 .left v')
              .faceNext (.inr d') (.inr e'))) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) := by
  obtain ⟨ℓ, m, ℓ', m', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid',
    hboundary, ho, hr, hc, hc'⟩ :=
    selectedCutPastCuts_representatives_left_retainedFace_stage_iff
      x T hT q s k K hk hK ha (β := β)
  refine ⟨ℓ, m, ℓ', m', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid',
    hboundary, ho, hr, ?_, hc, hc'⟩
  intro fv gv hP d e d' e' hd he
  let τ := selectedStageDartTransport w₀ ha R S I J
  have hτd : τ (cutLRepDartMap R hR d.1) = cutLRepDartMap S hS d'.1 := by
    apply J.toEquiv.injective
    exact (J.toEquiv.apply_symm_apply _).trans hd
  have hτe : τ (cutLRepDartMap R hR e.1) = cutLRepDartMap S hS e'.1 := by
    apply J.toEquiv.injective
    exact (J.toEquiv.apply_symm_apply _).trans he
  have hτinj : Function.Injective τ :=
    J.toEquiv.symm.injective.comp (image_stage_injective w₀ ha R I)
  have hret := hr fv gv hP d d' hd
  have hnext (hf : retainedFace (presentation (cutLRep R hR).2 .left v) d.1) :
      τ (cutLRepDartMap R hR
          ((cutLRep R hR).2.B.map.toCombinatorialMap.faceSucc d.1)) =
        cutLRepDartMap S hS
          ((cutLRep S hS).2.B.map.toCombinatorialMap.faceSucc d'.1) := by
    have hc := selectedStageDartTransport_faceSucc w₀ ha R S I J
      (cutLRepDartMap R hR d.1) (image_cutL_nonouter R hR d.1 hf.1)
    change τ (R.B.map.toCombinatorialMap.faceSucc (cutLRepDartMap R hR d.1)) =
      S.B.map.toCombinatorialMap.faceSucc (τ (cutLRepDartMap R hR d.1)) at hc
    rw [cutLRep_retainedFace_faceSucc_map R hR v d.1 hf, hc, hτd,
      cutLRep_retainedFace_faceSucc_map S hS v' d'.1 (hret.mp hf)]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · rintro ⟨hf, hde⟩
    refine ⟨hret.mp hf, (cutLRep_embedding_fields S hS).1 ?_⟩
    exact (hnext hf).symm.trans
      ((congrArg (τ ∘ cutLRepDartMap R hR) hde).trans hτe)
  · rintro ⟨hf, hde⟩
    have hf' := hret.mpr hf
    refine ⟨hf', ((hτinj.comp (cutLRep_embedding_fields R hR).1) ?_)⟩
    exact (hnext hf').trans
      ((congrArg (cutLRepDartMap S hS) hde).trans hτe.symm)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual left ancestor restrictions are fully marked isomorphic under the common prefix. -/
theorem selectedCutPastCuts_representatives_left_restriction_iso
    (ha : t₀ ≤ N₀) {β : Type*} :
    ∃ (ℓ d ℓ' d' : ℕ)
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
      (v : MapVertex (cutLRep R hR).2.B.map)
      (v' : MapVertex (cutLRep S hS).2.B.map),
      boundaryTarget (cutLRep R hR).2.B .left s = some v ∧
      boundaryTarget (cutLRep S hS).2.B .left s = some v' ∧
      (stageMapVertex w₀ t₀
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (stageMapVertex w₀ N₀
        (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        ∃ e : TruncationCell (presentation (cutLRep R hR).2 .left v) ≃
          TruncationCell (presentation (cutLRep S hS).2 .left v'),
          ∀ tag b c, truncationRelation (presentation (cutLRep R hR).2 .left v) tag b c ↔
            truncationRelation (presentation (cutLRep S hS).2 .left v') tag (e b) (e c)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) := by
  obtain ⟨ℓ, m, ℓ', m', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid',
    hboundary, _ho, _hr, hface, hc, hc'⟩ :=
    selectedCutPastCuts_representatives_left_faceNext_stage_iff
      x T hT q s k K hk hK ha (β := β)
  refine ⟨ℓ, m, ℓ', m', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', ?_, hc, hc'⟩
  intro fv gv hP
  obtain ⟨_, _, _, _, _, _, _, hRneg, hL, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let u := natSelect (fun m => ∀ j, m < j → L w₀ m + 1 ≤ L w₀ j) s
  have hb := selectedCut_boundary_target_record x T hT q .left k s hk
  have hb' := selectedCut_boundary_target_record x T hT q .left K s hK
  have hu : u ≤ t₀ := by
    have hh : u < (selectedCutTime T (k + 1) q.1).toNat := hb.1
    omega
  have hvid := hid.trans (congrArg PresentVertex.id hb.2).symm
  have hvid' := hid'.trans (congrArg PresentVertex.id hb'.2).symm
  obtain ⟨ev, hev⟩ := cutLRep_ancestors_stage_equiv w₀ ha R hR S hS I J fv gv hP
    hL hRneg u hu v v' hvid hvid'
  obtain ⟨ed, hed⟩ := cutLRep_selectedDarts_stage_equiv w₀ ha R hR S hS I J fv gv hP
    hL hRneg u hu v v' hvid hvid'
  have hℓ : s + 1 ≤ ℓ := by
    obtain ⟨l, d, A, hA, hl, _, _, hcA⟩ :=
      selectedCutPastCuts_representatives_stageIso x T hT q k s hk
    have he : ℓ = l := Option.some.inj (congrArg
      (fun c : PositiveCutOutput =>
        c.1.map (fun z : Σ r : ℕ, AllBoltzmannSpace r => Sigma.fst z.2)) (hc.symm.trans hcA))
    exact he.symm ▸ hl
  have hℓ' : s + 1 ≤ ℓ' := by
    obtain ⟨l, d, A, hA, hl, _, _, hcA⟩ :=
      selectedCutPastCuts_representatives_stageIso x T hT q K s hK
    have he : ℓ' = l := Option.some.inj (congrArg
      (fun c : PositiveCutOutput =>
        c.1.map (fun z : Σ r : ℕ, AllBoltzmannSpace r => Sigma.fst z.2)) (hc'.symm.trans hcA))
    exact he.symm ▸ hl
  let P := presentation (cutLRep R hR).2 .left v
  let Q := presentation (cutLRep S hS).2 .left v'
  let f := (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv) ∘
    cutLRepDartMap R hR
  let g := J.toEquiv ∘ cutLRepDartMap S hS
  have hf : Function.Injective f :=
    (image_stage_injective w₀ ha R I).comp (cutLRep_embedding_fields R hR).1
  have hg : Function.Injective g :=
    J.toEquiv.injective.comp (cutLRep_embedding_fields S hS).1
  have hfi (d) : f ((cutLRep R hR).2.B.map.edgeInv d) = edgeFlip _ (f d) := by
    dsimp only [f, Function.comp_apply]
    rw [(cutLRep_embedding_fields R hR).2.2.1, I.edgeInv_comm]
    rfl
  have hgi (d) : g ((cutLRep S hS).2.B.map.edgeInv d) = edgeFlip _ (g d) := by
    dsimp only [g, Function.comp_apply]
    rw [(cutLRep_embedding_fields S hS).2.2.1, J.edgeInv_comm]
    rfl
  have hmark (z) := cutLRep_ancestor_marks_stage_iff w₀ ha R hR S hS I J fv gv hP
    hL hRneg u hu v v' hvid hvid' z (ev z) (hev z)
  have hseam := cutLRep_selected_seam_stage_image_eq w₀ ha R hR S hS I J fv gv hP
    hL hRneg u s hu hℓ hℓ' v v' hv hv' hvid hvid'
  let e : TruncationCell P ≃ TruncationCell Q := Equiv.sumCongr ev ed
  refine ⟨e, ?_⟩
  intro tag b c
  cases tag with
  | vertex => cases b <;> cases c <;> rfl
  | root =>
      cases b with
      | inl z => exact (hmark z).1
      | inr d => cases c <;> rfl
  | target =>
      cases b with
      | inl z => exact (hmark z).2.1
      | inr d => cases c <;> rfl
  | incident =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          cases c with
          | inl z => exact (hmark z).2.2 d (ed d) (hed d)
          | inr z => rfl
  | opposite =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          cases c with
          | inl z => rfl
          | inr z =>
              change (_ = _) ↔ (_ = _)
              rw [← hf.eq_iff, ← hg.eq_iff, hfi, hgi]
              change edgeFlip _ (f d.1) = f z.1 ↔
                edgeFlip _ (g (ed d).1) = g (ed z).1
              rw [show f d.1 = g (ed d).1 from hed d,
                show f z.1 = g (ed z).1 from hed z]
  | oriented =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          change (cutLRep R hR).2.B.map.tail d.1 ↔
            (cutLRep S hS).2.B.map.tail (ed d).1
          rw [(cutLRep_embedding_fields R hR).2.2.2.1,
            (cutLRep_embedding_fields S hS).2.2.2.1,
            image_stage_tail_side w₀ R I, image_stage_tail_side w₀ S J]
          exact Iff.of_eq (congrArg
            (fun d : StageDart (kmswStage w₀ N₀).nextEdge => d.2 = false) (hed d))
  | rotation =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          cases c with
          | inl z => rfl
          | inr z =>
              exact cutLRep_truncation_rotation_stage_iff
                w₀ ha R hR S hS I J fv gv hP hL hRneg u hu v v' hvid hvid'
                d z (ed d) (ed z) (hed d) (hed z)
  | faceNext =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          cases c with
          | inl z => rfl
          | inr z => exact hface fv gv hP d z (ed d) (ed z) (hed d) (hed z)
  | boundary i =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d => exact hboundary d (ed d) (hed d) i
  | seam i =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d => exact image_mark_index_iff f g hf hg _ _ _ _ hseam d (ed d) (hed d) i

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual right ancestor restrictions are fully marked isomorphic under the common prefix. -/
theorem selectedCutPastCuts_representatives_right_restriction_iso
    (ha : t₀ ≤ N₀) {β : Type*} :
    ∃ (ℓ d ℓ' d' : ℕ)
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
      (v : MapVertex (cutRRep R hR).2.B.map)
      (v' : MapVertex (cutRRep S hS).2.B.map),
      boundaryTarget (cutRRep R hR).2.B .right s = some v ∧
      boundaryTarget (cutRRep S hS).2.B .right s = some v' ∧
      (stageMapVertex w₀ t₀
        (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id =
          edgeWest w₀ (kmswRightBoundaryEdge w₀ s) ∧
      (stageMapVertex w₀ N₀
        (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id =
          edgeWest w₀ (kmswRightBoundaryEdge w₀ s) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        ∃ e : TruncationCell (presentation (cutRRep R hR).2 .right v) ≃
          TruncationCell (presentation (cutRRep S hS).2 .right v'),
          ∀ tag b c, truncationRelation (presentation (cutRRep R hR).2 .right v) tag b c ↔
            truncationRelation (presentation (cutRRep S hS).2 .right v') tag (e b) (e c)) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) := by
  obtain ⟨ℓ, m, R, hR, I, _, v, _, hr, _, hv, _, hid, _, hbmark, hc⟩ :=
    image_representatives_both_boundary_targets x T hT q k s hk
  obtain ⟨ℓ', m', S, hS, J, _, v', _, hr', _, hv', _, hid', _, hbmark', hc'⟩ :=
    image_representatives_both_boundary_targets x T hT q K s hK
  refine ⟨ℓ, m, ℓ', m', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', ?_, hc, hc'⟩
  intro fv gv hP
  obtain ⟨_, _, _, _, _, _, _, hRneg, hL, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let u := natSelect (fun m => ∀ j, j < m → KMSW.R w₀ m < KMSW.R w₀ j) s
  have hb := selectedCut_boundary_target_record x T hT q .right k s hk
  have hb' := selectedCut_boundary_target_record x T hT q .right K s hK
  have hu : u ≤ t₀ := by
    have hh : u < (selectedCutTime T (k + 1) q.1).toNat := hb.1
    omega
  have hvid := hid.trans (congrArg PresentVertex.id hb.2).symm
  have hvid' := hid'.trans (congrArg PresentVertex.id hb'.2).symm
  obtain ⟨ev, hev⟩ := cutRRep_ancestors_stage_equiv w₀ ha R hR S hS I J fv gv hP
    hL hRneg u hu v v' hvid hvid'
  obtain ⟨ed, hed⟩ := cutRRep_selectedDarts_stage_equiv w₀ ha R hR S hS I J fv gv hP
    hL hRneg u hu v v' hvid hvid'
  let P := presentation (cutRRep R hR).2 .right v
  let Q := presentation (cutRRep S hS).2 .right v'
  let f := (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv) ∘
    cutRRepDartMap R hR
  let g := J.toEquiv ∘ cutRRepDartMap S hS
  have hf : Function.Injective f :=
    (image_stage_injective w₀ ha R I).comp (cutRRep_embedding_fields R hR).1
  have hg : Function.Injective g :=
    J.toEquiv.injective.comp (cutRRep_embedding_fields S hS).1
  have hfi (d) : f ((cutRRep R hR).2.B.map.edgeInv d) = edgeFlip _ (f d) := by
    dsimp only [f, Function.comp_apply]
    rw [(cutRRep_embedding_fields R hR).2.2.1, I.edgeInv_comm]
    rfl
  have hgi (d) : g ((cutRRep S hS).2.B.map.edgeInv d) = edgeFlip _ (g d) := by
    dsimp only [g, Function.comp_apply]
    rw [(cutRRep_embedding_fields S hS).2.2.1, J.edgeInv_comm]
    rfl
  have hmark (z) := cutRRep_ancestor_marks_stage_iff w₀ ha R hR S hS I J fv gv hP
    hL hRneg u hu v v' hvid hvid' z (ev z) (hev z)
  have hseam := cutRRep_selected_seam_stage_image_eq w₀ ha R hR S hS I J fv gv hP
    hL hRneg u s hu hr hr' v v' hv hv' hvid hvid'
  let e : TruncationCell P ≃ TruncationCell Q := Equiv.sumCongr ev ed
  refine ⟨e, ?_⟩
  intro tag b c
  cases tag with
  | vertex => cases b <;> cases c <;> rfl
  | root =>
      cases b with
      | inl z => exact (hmark z).1
      | inr d => cases c <;> rfl
  | target =>
      cases b with
      | inl z => exact (hmark z).2.1
      | inr d => cases c <;> rfl
  | incident =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          cases c with
          | inl z => exact (hmark z).2.2 d (ed d) (hed d)
          | inr z => rfl
  | opposite =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          cases c with
          | inl z => rfl
          | inr z =>
              change (_ = _) ↔ (_ = _)
              rw [← hf.eq_iff, ← hg.eq_iff, hfi, hgi]
              change edgeFlip _ (f d.1) = f z.1 ↔
                edgeFlip _ (g (ed d).1) = g (ed z).1
              rw [show f d.1 = g (ed d).1 from hed d,
                show f z.1 = g (ed z).1 from hed z]
  | oriented =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          change (cutRRep R hR).2.B.map.tail d.1 ↔
            (cutRRep S hS).2.B.map.tail (ed d).1
          rw [(cutRRep_embedding_fields R hR).2.2.2.1,
            (cutRRep_embedding_fields S hS).2.2.2.1,
            image_stage_tail_side w₀ R I, image_stage_tail_side w₀ S J]
          exact Iff.of_eq (congrArg
            (fun d : StageDart (kmswStage w₀ N₀).nextEdge => d.2 = false) (hed d))
  | rotation =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          cases c with
          | inl z => rfl
          | inr z =>
              exact cutRRep_truncation_rotation_stage_iff
                w₀ ha R hR S hS I J fv gv hP hL hRneg u hu v v' hvid hvid'
                d z (ed d) (ed z) (hed d) (hed z)
  | faceNext =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          cases c with
          | inl z => rfl
          | inr z =>
              exact cutRRep_truncation_faceNext_stage_iff w₀ ha R hR S hS I J fv gv hP
                hL hRneg u hu v v' hvid hvid' d z (ed d) (ed z) (hed d) (hed z)
  | boundary i =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d =>
          let fi := fun b => ((I.toEquiv (cutRRepDartMap R hR b)).1.val,
            (I.toEquiv (cutRRepDartMap R hR b)).2)
          let gi := fun b => ((J.toEquiv (cutRRepDartMap S hS b)).1.val,
            (J.toEquiv (cutRRepDartMap S hS b)).2)
          have hfi' : Function.Injective fi := by
            intro a b h
            apply (cutRRep_embedding_fields R hR).1
            apply I.toEquiv.injective
            exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) h))
              (congrArg (fun z : ℕ × Bool => z.2) h)
          have hgi' : Function.Injective gi := by
            intro a b h
            apply (cutRRep_embedding_fields S hS).1
            apply J.toEquiv.injective
            exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) h))
              (congrArg (fun z : ℕ × Bool => z.2) h)
          exact image_mark_index_iff fi gi hfi' hgi' _ _ _ _
            (fun i z => (hbmark i z).trans (hbmark' i z).symm) d (ed d)
            (congrArg (fun z : StageDart (kmswStage w₀ N₀).nextEdge =>
              (z.1.val, z.2)) (hed d)) i
  | seam i =>
      cases b with
      | inl z => cases c <;> rfl
      | inr d => exact image_mark_index_iff f g hf hg _ _ _ _ hseam d (ed d) (hed d) i

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The marked restriction isomorphism gives equality of the actual cut truncations. -/
theorem selectedCutPastCuts_representatives_left_halfTruncate_eq
    (ha : t₀ ≤ N₀) {β : Type*} :
    ∃ (ℓ d ℓ' d' : ℕ)
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
      (v : MapVertex (cutLRep R hR).2.B.map)
      (v' : MapVertex (cutLRep S hS).2.B.map),
      boundaryTarget (cutLRep R hR).2.B .left s = some v ∧
      boundaryTarget (cutLRep S hS).2.B .left s = some v' ∧
      (stageMapVertex w₀ t₀
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (stageMapVertex w₀ N₀
        (cutMapIsoVertexEquiv J (cutLRepVertexMap S hS v'))).id =
          edgeWest w₀ (kmswLeftBoundaryEdge w₀ s) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        halfTruncate .left s (selectedCutPastCuts x T (k + 1) q.1).1 =
          halfTruncate .left s (selectedCutPastCuts x T (K + 1) q.1).1) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', hiso, hc, hc'⟩ :=
    selectedCutPastCuts_representatives_left_restriction_iso
      x T hT q s k K hk hK ha (β := β)
  refine ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', ?_, hc, hc'⟩
  intro fv gv hP
  obtain ⟨e, he⟩ := hiso fv gv hP
  rw [hc, hc']
  exact halfTruncate_some_mk_eq_of_restriction_iso
    (cutLRep R hR).2 (cutLRep S hS).2 .left s v v' hv hv' e he

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The marked restriction isomorphism gives equality of the actual cut truncations. -/
theorem selectedCutPastCuts_representatives_right_halfTruncate_eq
    (ha : t₀ ≤ N₀) {β : Type*} :
    ∃ (ℓ d ℓ' d' : ℕ)
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w₀ t₀))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w₀ N₀))
      (v : MapVertex (cutRRep R hR).2.B.map)
      (v' : MapVertex (cutRRep S hS).2.B.map),
      boundaryTarget (cutRRep R hR).2.B .right s = some v ∧
      boundaryTarget (cutRRep S hS).2.B .right s = some v' ∧
      (stageMapVertex w₀ t₀
        (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id =
          edgeWest w₀ (kmswRightBoundaryEdge w₀ s) ∧
      (stageMapVertex w₀ N₀
        (cutMapIsoVertexEquiv J (cutRRepVertexMap S hS v'))).id =
          edgeWest w₀ (kmswRightBoundaryEdge w₀ s) ∧
      (∀ (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β),
        CommonSelectedPrefix R hR S hS
          (outerSucc_castDart (kmswStage_nextEdge_mono w₀ ha) ∘ I.toEquiv)
          J.toEquiv fv gv →
        halfTruncate .right s (selectedCutPastCuts x T (k + 1) q.1).2 =
          halfTruncate .right s (selectedCutPastCuts x T (K + 1) q.1).2) ∧
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) := by
  obtain ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', hiso, hc, hc'⟩ :=
    selectedCutPastCuts_representatives_right_restriction_iso
      x T hT q s k K hk hK ha (β := β)
  refine ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', hv, hv', hid, hid', ?_, hc, hc'⟩
  intro fv gv hP
  obtain ⟨e, he⟩ := hiso fv gv hP
  rw [hc, hc']
  exact halfTruncate_some_mk_eq_of_restriction_iso
    (cutRRep R hR).2 (cutRRep S hS).2 .right s v v' hv hv' e he

end SelectedCuts


















end DirectedDistances.PaperProofs.Section4
