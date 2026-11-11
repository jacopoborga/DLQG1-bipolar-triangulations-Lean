module

public import DirectedDistances.PaperProofs.Section4.ThinCutSideCarrierCompatibility
public import DirectedDistances.PlanarMap.PlanarPathCutLeftmostRegion
public import DirectedDistances.KMSW.StageTrianglePersistence

import DirectedDistances.PaperProofs.Section3.KMSWBdyFinal

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

The common-stage dart transport and the pullback of the later left-region color.
Common selected prefixes give the path seed colors and exact seam transport.
The left outer-arc colors follow by backward induction through triangle attachments,
using the final-stage rank to exclude fresh seam edges below the old sink.
All coloring conditions hold, giving preservation and reflection of the left
closure and both edge-closed half carriers. These are finite transport helpers;
the common-prefix bridge to the infinite selected geodesic is a separate obligation. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open scoped Classical

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected prefix sends every earlier path dart to a later path dart. -/
theorem commonSelectedPrefix_pathDart_image
    {x : XDP} {ℓ r n m ℓ' r' n' m' : ℕ} {α β : Type*}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (fd : Fin R.dartCount → α) (gd : Fin S.dartCount → α)
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS fd gd fv gv)
    (e : Fin R.dartCount) (he : e ∈ (selectedGeodesicOfLen R.B x hR).darts) :
    fd e ∈ gd '' {e' | e' ∈ (selectedGeodesicOfLen S.B x hS).darts} := by
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
  have him : i < m := by
    simpa only [(selectedGeodesicOfLen R.B x hR).darts_length] using hi
  obtain ⟨d, d', hd, hd', hdd'⟩ := hP.2.1 i him
  have hget : (selectedGeodesicOfLen R.B x hR).darts[i]? = some e := by
    rw [List.getElem?_eq_getElem hi, hie]
  have hde : d = e := Option.some.inj (hd.symm.trans hget)
  subst d
  exact ⟨d', List.mem_of_getElem? hd', hdd'.symm⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Transport through the old stage, its coordinate inclusion, and the later representative. -/
@[expose] def selectedStageDartTransport
    {ℓ r n ℓ' r' n' a N : ℕ} (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N)) :
    Fin R.dartCount → Fin S.dartCount :=
  J.toEquiv.symm ∘ outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The left-region color, before adjoining both seam darts to form the closed half. -/
@[expose] noncomputable def selectedCutLeftColor
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (e : Fin R.dartCount) : Bool :=
  decide (e ∈ pathCutLeftDarts R.B (selectedGeodesicOfLen R.B x hR))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The coloring of the earlier darts pulled back from the later left region. -/
@[expose] noncomputable def selectedStageLeftColor
    {x : XDP} {ℓ r n ℓ' r' n' m' a N : ℕ}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : Fin R.dartCount) : Bool :=
  selectedCutLeftColor S hS (selectedStageDartTransport w ha R S I J e)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual coordinate transport commutes with reversal of geometric edge darts. -/
theorem selectedStageDartTransport_edgeInv
    {ℓ r n ℓ' r' n' a N : ℕ} (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : Fin R.dartCount) :
    selectedStageDartTransport w ha R S I J (R.B.map.toCombinatorialMap.edgeInv e) =
      S.B.map.toCombinatorialMap.edgeInv (selectedStageDartTransport w ha R S I J e) := by
  apply J.toEquiv.injective
  simp only [selectedStageDartTransport, Function.comp_apply, Equiv.apply_symm_apply,
    J.edgeInv_comm]
  rw [I.edgeInv_comm]
  rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The pullback color is true on every directed dart of the common selected prefix. -/
theorem selectedStageLeftColor_pathDart
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)
    (e : Fin R.dartCount) (he : e ∈ (selectedGeodesicOfLen R.B x hR).darts) :
    selectedCutLeftColor S hS (selectedStageDartTransport w ha R S I J e) = true := by
  obtain ⟨d, hd, hde⟩ := commonSelectedPrefix_pathDart_image R hR S hS _ _ fv gv hP e he
  have ht : selectedStageDartTransport w ha R S I J e = d := by
    apply J.toEquiv.injective
    simpa only [selectedStageDartTransport, Function.comp_apply,
      Equiv.apply_symm_apply] using hde.symm
  rw [ht]
  simpa only [selectedCutLeftColor, decide_eq_true_eq] using
    pathCut_pathDart_mem_left S.B (selectedGeodesicOfLen S.B x hS) hd

private theorem selectedCutLeftColor_spec
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) :
    let P := selectedGeodesicOfLen R.B x hR
    (∀ d, d ∈ pathCutLeftSeeds R.B P → selectedCutLeftColor R hR d = true) ∧
      (∀ d, d ∈ pathCutRightSeeds R.B P → selectedCutLeftColor R hR d = false) ∧
      (∀ d, ¬ R.B.map.IsOuter d →
        selectedCutLeftColor R hR (R.B.map.toCombinatorialMap.faceSucc d) =
          selectedCutLeftColor R hR d) ∧
      (∀ d, d ∉ pathCutSeamDarts R.B P →
        selectedCutLeftColor R hR (R.B.map.toCombinatorialMap.edgeInv d) =
          selectedCutLeftColor R hR d) := by
  let P := selectedGeodesicOfLen R.B x hR
  obtain ⟨side, hl, hr, hf, he⟩ := pathCut_exists_side_coloring R.B P
  have hc (d : Fin R.dartCount) : selectedCutLeftColor R hR d = side d := by
    have hiff := pathCutLeft_mem_iff_side_true_of_sideColoring R.B P side hl hr hf he d
    cases hd : side d with
    | false =>
      have hn : d ∉ pathCutLeftDarts R.B P := by
        intro hm
        have ht := hiff.mp hm
        rw [hd] at ht
        cases ht
      change decide (d ∈ pathCutLeftDarts R.B P) = false
      simp only [hn, decide_false]
    | true =>
      have hm := hiff.mpr hd
      change decide (d ∈ pathCutLeftDarts R.B P) = true
      simp only [hm, decide_true]
  constructor
  · intro d hd
    rw [hc]
    exact hl d hd
  constructor
  · intro d hd
    rw [hc]
    exact hr d hd
  constructor
  · intro d hd
    rw [hc, hc]
    exact hf d hd
  · intro d hd
    rw [hc, hc]
    exact he d hd

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every earlier internal dart remains off the outer word at every later stage. -/
theorem selectedStage_castDart_not_outerWord
    (w : ℕ → Fin 3) {a N : ℕ} (ha : a ≤ N)
    (d : StageDart (kmswStage w a).nextEdge) (hd : d ∉ stageOuterWord w a) :
    outerSucc_castDart (kmswStage_nextEdge_mono w ha) d ∉ stageOuterWord w N := by
  rcases stage_dart_partition w a d with ho | ⟨j, hj, _⟩
  · exact (hd ho).elim
  · exact stageTriangleDart_not_outer w N j (lt_of_lt_of_le hj.1 ha) _ hj.2

private theorem selectedStage_faceSucc_not_outerWord
    (w : ℕ → Fin 3) (a : ℕ) (d : StageDart (kmswStage w a).nextEdge)
    (hd : d ∉ stageOuterWord w a) :
    (kmswMap w a).faceSucc d ∉ stageOuterWord w a := by
  intro hf
  let l := stageOuterWord w a
  let e := l.formPerm.symm ((kmswMap w a).faceSucc d)
  have he : e ∈ l := l.mem_of_formPerm_apply_mem (by
    simpa only [e, Equiv.apply_symm_apply] using hf)
  have hfe : (kmswMap w a).faceSucc e = (kmswMap w a).faceSucc d := by
    rw [stageOuterWord_faceSucc w a e he]
    exact l.formPerm.apply_symm_apply _
  exact hd ((kmswMap w a).faceSucc.injective hfe ▸ he)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Internal face successors commute with the inclusion into any later stage. -/
theorem selectedStage_faceSucc_castDart
    (w : ℕ → Fin 3) {a N : ℕ} (ha : a ≤ N)
    (d : StageDart (kmswStage w a).nextEdge) (hd : d ∉ stageOuterWord w a) :
    (kmswMap w N).faceSucc (outerSucc_castDart (kmswStage_nextEdge_mono w ha) d) =
      outerSucc_castDart (kmswStage_nextEdge_mono w ha) ((kmswMap w a).faceSucc d) := by
  have hfd := selectedStage_faceSucc_not_outerWord w a d hd
  induction N, ha using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    have hstep := stageFaceSucc_castDart_of_not_outer w N (stageOuterWord_faceSucc w N)
      (outerSucc_castDart (kmswStage_nextEdge_mono w hN) d)
      (by rw [ih]; exact selectedStage_castDart_not_outerWord w hN _ hfd)
    calc
      _ = (kmswMap w (N + 1)).faceSucc
          (outerSucc_castDart (kmswStage_nextEdge_mono w (Nat.le_succ N))
            (outerSucc_castDart (kmswStage_nextEdge_mono w hN) d)) := rfl
      _ = _ := hstep
      _ = _ := congrArg (outerSucc_castDart
        (kmswStage_nextEdge_mono w (Nat.le_succ N))) ih
      _ = _ := rfl

private theorem color_iso_faceSucc
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {M' : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M M') (d : D) :
    I.toEquiv (M.toCombinatorialMap.faceSucc d) =
      M'.toCombinatorialMap.faceSucc (I.toEquiv d) := by
  have hr (e : D) : I.toEquiv (M.rot.symm e) = M'.rot.symm (I.toEquiv e) := by
    apply M'.rot.injective
    rw [← I.rot_comm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change I.toEquiv (M.rot.symm (M.edgeInv d)) = M'.rot.symm (M'.edgeInv (I.toEquiv d))
  rw [hr, I.edgeInv_comm]

private theorem color_stageOuter_iff (w : ℕ → Fin 3) (a : ℕ)
    (d : StageDart (kmswStage w a).nextEdge) :
    d ∈ stageOuterWord w a ↔ (kmswStageDirectedMap w a).IsOuter d := by
  exact mem_iff_isOuter _ _ (Section3.kmsw_bdy_source_four_arcs w a).1.1 d

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An internal representative dart remains internal after common-stage transport. -/
theorem selectedStageDartTransport_not_outer
    {ℓ r n ℓ' r' n' a N : ℕ} (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : Fin R.dartCount) (he : ¬ R.B.map.IsOuter e) :
    ¬ S.B.map.IsOuter (selectedStageDartTransport w ha R S I J e) := by
  have hi : I.toEquiv e ∉ stageOuterWord w a := by
    intro ho
    exact he ((I.outer_iff e).mp ((color_stageOuter_iff w a _).mp ho))
  have hn := selectedStage_castDart_not_outerWord w ha (I.toEquiv e) hi
  intro ho
  apply hn
  apply (color_stageOuter_iff w N _).mpr
  have hj := (J.outer_iff (selectedStageDartTransport w ha R S I J e)).mpr ho
  simpa only [selectedStageDartTransport, Function.comp_apply,
    Equiv.apply_symm_apply] using hj

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The common-stage representative transport preserves every internal face successor. -/
theorem selectedStageDartTransport_faceSucc
    {ℓ r n ℓ' r' n' a N : ℕ} (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : Fin R.dartCount) (he : ¬ R.B.map.IsOuter e) :
    selectedStageDartTransport w ha R S I J (R.B.map.toCombinatorialMap.faceSucc e) =
      S.B.map.toCombinatorialMap.faceSucc (selectedStageDartTransport w ha R S I J e) := by
  have hi : I.toEquiv e ∉ stageOuterWord w a := by
    intro ho
    exact he ((I.outer_iff e).mp ((color_stageOuter_iff w a _).mp ho))
  apply J.toEquiv.injective
  rw [color_iso_faceSucc J]
  simp only [selectedStageDartTransport, Function.comp_apply, Equiv.apply_symm_apply]
  rw [color_iso_faceSucc I]
  exact (selectedStage_faceSucc_castDart w ha (I.toEquiv e) hi).symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The pullback of the later left color satisfies the earlier internal-face axiom. -/
theorem selectedStageLeftColor_faceSucc
    {x : XDP} {ℓ r n ℓ' r' n' m' a N : ℕ}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : Fin R.dartCount) (he : ¬ R.B.map.IsOuter e) :
    selectedCutLeftColor S hS
        (selectedStageDartTransport w ha R S I J (R.B.map.toCombinatorialMap.faceSucc e)) =
      selectedCutLeftColor S hS (selectedStageDartTransport w ha R S I J e) := by
  rw [selectedStageDartTransport_faceSucc w ha R S I J e he]
  exact (selectedCutLeftColor_spec S hS).2.2.1 _
    (selectedStageDartTransport_not_outer w ha R S I J e he)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual representative transport sends every prefix path dart into the later path. -/
theorem selectedStageDartTransport_pathDart
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)
    (e : Fin R.dartCount) (he : e ∈ (selectedGeodesicOfLen R.B x hR).darts) :
    selectedStageDartTransport w ha R S I J e ∈ (selectedGeodesicOfLen S.B x hS).darts := by
  obtain ⟨d, hd, hde⟩ := commonSelectedPrefix_pathDart_image R hR S hS _ _ fv gv hP e he
  have ht : selectedStageDartTransport w ha R S I J e = d := by
    apply J.toEquiv.injective
    simpa only [selectedStageDartTransport, Function.comp_apply,
      Equiv.apply_symm_apply] using hde.symm
  exact ht ▸ hd

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The pullback color is false on the reversals of the earlier directed path darts. -/
theorem selectedStageLeftColor_pathDart_flip
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)
    (e : Fin R.dartCount) (he : e ∈ (selectedGeodesicOfLen R.B x hR).darts) :
    selectedStageLeftColor w ha R S hS I J (R.B.map.toCombinatorialMap.edgeInv e) =
      false := by
  change selectedCutLeftColor S hS
    (selectedStageDartTransport w ha R S I J (R.B.map.toCombinatorialMap.edgeInv e)) = false
  rw [selectedStageDartTransport_edgeInv w ha R S I J]
  apply (selectedCutLeftColor_spec S hS).2.1
  exact Or.inr ⟨_, selectedStageDartTransport_pathDart w ha R hR S hS I J fv gv hP e he,
    rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both darts of every earlier seam edge remain on the later seam. -/
theorem selectedStageDartTransport_seam
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)
    (e : Fin R.dartCount)
    (he : e ∈ pathCutSeamDarts R.B (selectedGeodesicOfLen R.B x hR)) :
    selectedStageDartTransport w ha R S I J e ∈
      pathCutSeamDarts S.B (selectedGeodesicOfLen S.B x hS) := by
  rcases he with he | he
  · exact Or.inl (selectedStageDartTransport_pathDart w ha R hR S hS I J fv gv hP e he)
  · right
    rw [← selectedStageDartTransport_edgeInv w ha R S I J]
    exact selectedStageDartTransport_pathDart w ha R hR S hS I J fv gv hP _ he

private noncomputable def color_vertex
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    (w : ℕ → Fin 3) (a : ℕ)
    (I : DirectedMapWithMissingIso M (kmswStageDirectedMap w a))
    (v : MapVertex M) : PresentVertex w :=
  ⟨(stageMapVertex w a (cutMapIsoVertexEquiv I v)).id⟩

private theorem color_vertex_tail
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    (w : ℕ → Fin 3) (a : ℕ)
    (I : DirectedMapWithMissingIso M (kmswStageDirectedMap w a)) (d : D) :
    (color_vertex w a I (dartTailVertex M d)).id =
      if (I.toEquiv d).2 then edgeEast w (I.toEquiv d).1.val
      else edgeWest w (I.toEquiv d).1.val := by
  change (stageMapVertex w a
    (cutMapIsoVertexEquiv I (dartTailVertex M d))).id = _
  rw [(cutMapIsoVertexEquiv_endpoints I d).1, stageMapVertex_tail]
  unfold stageEndpoint
  rw [(edge_endpoints_eq w (I.toEquiv d).1.isLt).1,
    (edge_endpoints_eq w (I.toEquiv d).1.isLt).2]

private theorem color_vertex_head
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    (w : ℕ → Fin 3) (a : ℕ)
    (I : DirectedMapWithMissingIso M (kmswStageDirectedMap w a)) (d : D) :
    (color_vertex w a I (dartHeadVertex M d)).id =
      if (I.toEquiv d).2 then edgeWest w (I.toEquiv d).1.val
      else edgeEast w (I.toEquiv d).1.val := by
  change (color_vertex w a I (dartTailVertex M (M.edgeInv d))).id = _
  rw [color_vertex_tail, I.edgeInv_comm]
  change (if !(I.toEquiv d).2 then _ else _) = _
  cases (I.toEquiv d).2 <;> rfl

private theorem color_vertex_step
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    (w : ℕ → Fin 3) (a : ℕ)
    (I : DirectedMapWithMissingIso M (kmswStageDirectedMap w a))
    {u v : MapVertex M} (h : M.directedStep u v) :
    Nonempty (color_vertex w a I u ⟶ color_vertex w a I v) := by
  obtain ⟨d, _, ht, rfl, rfl⟩ := h
  have hd := (I.tail_iff d).mpr ht
  change (kmswStage w a).present (I.toEquiv d).1.val = true ∧
    (I.toEquiv d).2 = false at hd
  refine ⟨⟨(I.toEquiv d).1.val, ⟨a, (I.toEquiv d).1.isLt, hd.1⟩, ?_, ?_⟩⟩
  · change edgeWest w (I.toEquiv d).1.val =
      (color_vertex w a I (dartTailVertex M d)).id
    rw [color_vertex_tail w a I d, hd.2]
    rfl
  · change edgeEast w (I.toEquiv d).1.val =
      (color_vertex w a I (dartHeadVertex M d)).id
    rw [color_vertex_head w a I d, hd.2]
    rfl

private theorem color_vertex_reach
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    (w : ℕ → Fin 3) (a : ℕ)
    (I : DirectedMapWithMissingIso M (kmswStageDirectedMap w a))
    {u v : MapVertex M} (h : Relation.ReflTransGen M.directedStep u v) :
    Reachable (color_vertex w a I u) (color_vertex w a I v) := by
  induction h with
  | refl => exact Reachable.rfl
  | tail _ hs ih =>
    obtain ⟨e⟩ := color_vertex_step w a I hs
    exact ih.trans e.reachable

private theorem color_path_segment
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    {u v : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M u v n)
    (i d : ℕ) (hid : i + d ≤ n) :
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

private theorem color_transport_endpoints
    {ℓ r n ℓ' r' n' a N : ℕ} (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : Fin R.dartCount) :
    color_vertex w a I (dartTailVertex R.B.map e) =
        color_vertex w N J (dartTailVertex S.B.map
          (selectedStageDartTransport w ha R S I J e)) ∧
      color_vertex w a I (dartHeadVertex R.B.map e) =
        color_vertex w N J (dartHeadVertex S.B.map
          (selectedStageDartTransport w ha R S I J e)) := by
  constructor <;> apply congrArg PresentVertex.mk
  · change (color_vertex w a I (dartTailVertex R.B.map e)).id =
      (color_vertex w N J (dartTailVertex S.B.map
        (selectedStageDartTransport w ha R S I J e))).id
    rw [color_vertex_tail w a I e,
      color_vertex_tail w N J (selectedStageDartTransport w ha R S I J e)]
    simp only [selectedStageDartTransport, Function.comp_apply, Equiv.apply_symm_apply]
    rfl
  · change (color_vertex w a I (dartHeadVertex R.B.map e)).id =
      (color_vertex w N J (dartHeadVertex S.B.map
        (selectedStageDartTransport w ha R S I J e))).id
    rw [color_vertex_head w a I e,
      color_vertex_head w N J (selectedStageDartTransport w ha R S I J e)]
    simp only [selectedStageDartTransport, Function.comp_apply, Equiv.apply_symm_apply]
    rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A later path dart in the old carrier already belongs to the common prefix.
The old sink and acyclicity exclude every old dart from the later suffix. -/
theorem selectedStageDartTransport_pathDart_reflect
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)
    (e : Fin R.dartCount)
    (he : selectedStageDartTransport w ha R S I J e ∈
      (selectedGeodesicOfLen S.B x hS).darts) :
    e ∈ (selectedGeodesicOfLen R.B x hR).darts := by
  let P := selectedGeodesicOfLen R.B x hR
  let Q := selectedGeodesicOfLen S.B x hS
  let τ := selectedStageDartTransport w ha R S I J
  have hinj : Function.Injective τ := by
    intro d d' h
    apply I.toEquiv.injective
    have hh := congrArg J.toEquiv h
    simp only [τ, selectedStageDartTransport, Function.comp_apply,
      Equiv.apply_symm_apply] at hh
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z => z.1.val) hh
    · exact congrArg (fun z : StageDart (kmswStage w N).nextEdge => z.2) hh
  have hmm' := hP.1
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    have hsame : P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ =
        P.vertices.get ⟨m, by rw [P.vertices_length]; omega⟩ := by
      exact congrArg P.vertices.get (Fin.ext hm0.symm)
    exact bipolar_source_ne_sink R.B
      (P.start_vertex.symm.trans (hsame.trans P.end_vertex))
  obtain ⟨d, d', hd, hd', hdd'⟩ := hP.2.1 (m - 1) (by omega)
  have hdget : P.darts.get ⟨m - 1, by rw [P.darts_length]; omega⟩ = d := by
    exact Option.some.inj ((List.getElem?_eq_getElem
      (by rw [P.darts_length]; omega : m - 1 < P.darts.length)).symm.trans hd)
  have hdget' : Q.darts.get ⟨m - 1, by rw [Q.darts_length]; omega⟩ = d' := by
    exact Option.some.inj ((List.getElem?_eq_getElem
      (by rw [Q.darts_length]; omega : m - 1 < Q.darts.length)).symm.trans hd')
  have hτd : τ d = d' := by
    apply J.toEquiv.injective
    simpa only [τ, selectedStageDartTransport, Function.comp_apply,
      Equiv.apply_symm_apply] using hdd'
  have hsink : color_vertex w a I R.B.sink =
      color_vertex w N J (Q.vertices.get ⟨m, by rw [Q.vertices_length]; omega⟩) := by
    have hp := (P.edge_step ⟨m - 1, by rw [P.darts_length]; omega⟩).2.2.2
    have hq := (Q.edge_step ⟨m - 1, by rw [Q.darts_length]; omega⟩).2.2.2
    have hlast : m - 1 + 1 = m := by omega
    simp only [hlast, hdget, P.end_vertex] at hp
    simp only [hlast, hdget'] at hq
    rw [hp, hq, ← hτd]
    exact (color_transport_endpoints w ha R S I J d).2
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
  have him' : i < m' := lt_of_lt_of_eq hi Q.darts_length
  by_cases him : i < m
  · obtain ⟨f, f', hf, hf', hff'⟩ := hP.2.1 i him
    have hiopt : Q.darts[i]? = some (τ e) := by
      rw [List.getElem?_eq_getElem hi, hie]
    have hfe : f' = τ e := Option.some.inj (hf'.symm.trans hiopt)
    have hτf : τ f = f' := by
      apply J.toEquiv.injective
      simpa only [τ, selectedStageDartTransport, Function.comp_apply,
        Equiv.apply_symm_apply] using hff'
    have hfe' : f = e := hinj (hτf.trans hfe)
    exact hfe' ▸ List.mem_of_getElem? hf
  · have hmi : m ≤ i := by omega
    have hseg := color_vertex_reach w N J (color_path_segment Q m (i - m) (by omega))
    have hidx : m + (i - m) = i := by omega
    simp only [hidx] at hseg
    have hstep := Q.edge_step ⟨i, hi⟩
    have hget : Q.darts.get ⟨i, hi⟩ = τ e := hie
    rw [hget] at hstep
    rw [hstep.2.2.1, ← hsink,
      ← (color_transport_endpoints w ha R S I J e).1] at hseg
    obtain ⟨q⟩ := hseg
    obtain ⟨edge⟩ := color_vertex_step w N J
      (show S.B.map.directedStep (dartTailVertex S.B.map (τ e))
        (dartHeadVertex S.B.map (τ e)) from
          ⟨τ e, hstep.1, hstep.2.1, rfl, rfl⟩)
    obtain ⟨k, H, _⟩ := exists_simple_sink_pathBase R.B (dartHeadVertex R.B.map e)
    have hback := color_vertex_reach w a I (color_path_segment H 0 k (by omega))
    simp only [Nat.zero_add, H.start_vertex, H.end_vertex] at hback
    obtain ⟨back⟩ := hback
    have hends := color_transport_endpoints w ha R S I J e
    rw [← hends.1, ← hends.2] at edge
    have hcycle := presentVertex_acyclic w _ ((q.comp edge.toPath).comp back)
    simp only [Path.length_comp, Path.length_toPath] at hcycle
    omega

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A later seam dart in the old carrier is already on the earlier seam. -/
theorem selectedStageDartTransport_seam_reflect
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)
    (e : Fin R.dartCount)
    (he : selectedStageDartTransport w ha R S I J e ∈
      pathCutSeamDarts S.B (selectedGeodesicOfLen S.B x hS)) :
    e ∈ pathCutSeamDarts R.B (selectedGeodesicOfLen R.B x hR) := by
  rcases he with he | he
  · exact Or.inl
      (selectedStageDartTransport_pathDart_reflect w ha R hR S hS I J fv gv hP e he)
  · right
    apply selectedStageDartTransport_pathDart_reflect w ha R hR S hS I J fv gv hP
    rw [selectedStageDartTransport_edgeInv]
    exact he

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The pullback color is invariant under reversing every earlier non-seam edge. -/
theorem selectedStageLeftColor_edgeInv
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv) :
    ∀ e, e ∉ pathCutSeamDarts R.B (selectedGeodesicOfLen R.B x hR) →
      selectedStageLeftColor w ha R S hS I J (R.B.map.edgeInv e) =
        selectedStageLeftColor w ha R S hS I J e := by
  intro e he
  change selectedCutLeftColor S hS
    (selectedStageDartTransport w ha R S I J (R.B.map.edgeInv e)) = _
  rw [selectedStageDartTransport_edgeInv]
  apply (selectedCutLeftColor_spec S hS).2.2.2
  intro ht
  exact he (selectedStageDartTransport_seam_reflect w ha R hR S hS I J fv gv hP e ht)

private theorem color_iso_lrDarts
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {M' : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M M') (d : D) :
    I.toEquiv d ∈ M'.lrDarts ↔ d ∈ M.lrDarts := by
  change (¬ M'.missing (I.toEquiv d) ∧ ¬ M'.tail (I.toEquiv d) ∧
    M'.IsOuter (I.toEquiv d)) ↔ (¬ M.missing d ∧ ¬ M.tail d ∧ M.IsOuter d)
  rw [I.missing_iff, I.tail_iff, I.outer_iff]

private theorem color_stageLR_mono
    (w : ℕ → Fin 3) {a N e : ℕ} (ha : a ≤ N)
    (he : e ∈ (kmswStage w a).LR) : e ∈ (kmswStage w N).LR := by
  induction N, ha using Nat.le_induction with
  | base => exact he
  | succ N _ ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w N
    rw [ht]
    exact List.mem_append_left _ ih

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every earlier right outer-arc dart remains on the later right outer arc. -/
theorem selectedStageDartTransport_rightOuterArc
    {ℓ r n ℓ' r' n' a N : ℕ} (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : Fin R.dartCount) (he : e ∈ pathCutRightOuterArc R.B) :
    selectedStageDartTransport w ha R S I J e ∈ pathCutRightOuterArc S.B := by
  have hi := (color_iso_lrDarts I e).mpr he
  obtain ⟨hside, hedge⟩ := (kmswStageLRDartsFinset_mem w a _).mp
    ((kmswStageLRDartsFinset_map_mem w a _).mpr hi)
  apply (color_iso_lrDarts J _).mp
  change J.toEquiv (J.toEquiv.symm
    (outerSucc_castDart (kmswStage_nextEdge_mono w ha) (I.toEquiv e))) ∈ _
  rw [Equiv.apply_symm_apply]
  apply (kmswStageLRDartsFinset_map_mem w N _).mp
  apply (kmswStageLRDartsFinset_mem w N _).mpr
  exact ⟨hside, color_stageLR_mono w ha hedge⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The pullback color is false on the entire earlier right outer arc. -/
theorem selectedStageLeftColor_rightOuterArc
    {x : XDP} {ℓ r n ℓ' r' n' m' a N : ℕ}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N)) :
    ∀ e ∈ pathCutRightOuterArc R.B, selectedStageLeftColor w ha R S hS I J e = false := by
  intro e he
  apply (selectedCutLeftColor_spec S hS).2.1
  exact Or.inl (selectedStageDartTransport_rightOuterArc w ha R S I J e he)

private theorem color_iso_ulDarts
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {M : DirectedMapWithMissing D} {M' : DirectedMapWithMissing E}
    (I : DirectedMapWithMissingIso M M') (d : D) :
    I.toEquiv d ∈ M'.ulDarts ↔ d ∈ M.ulDarts := by
  change (¬ M'.missing (I.toEquiv d) ∧ M'.tail (I.toEquiv d) ∧
    M'.IsOuter (I.toEquiv d)) ↔ (¬ M.missing d ∧ M.tail d ∧ M.IsOuter d)
  rw [I.missing_iff, I.tail_iff, I.outer_iff]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An earlier left outer dart that stays outer is a later left seed. -/
theorem selectedStageDartTransport_leftOuterArc_of_outer
    {ℓ r n ℓ' r' n' a N : ℕ} (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : Fin R.dartCount) (he : e ∈ pathCutLeftOuterArc R.B)
    (ho : S.B.map.IsOuter (selectedStageDartTransport w ha R S I J e)) :
    selectedStageDartTransport w ha R S I J e ∈ pathCutLeftOuterArc S.B := by
  have hi := (color_iso_ulDarts I e).mpr he
  have ht : (I.toEquiv e).2 = false := hi.2.1.2
  refine ⟨S.B.noMissingDarts _, ?_, ho⟩
  apply (J.tail_iff _).mp
  change (kmswStage w N).present
    (J.toEquiv (selectedStageDartTransport w ha R S I J e)).1.val = true ∧
    (J.toEquiv (selectedStageDartTransport w ha R S I J e)).2 = false
  constructor
  · have hn := S.B.noMissingDarts (selectedStageDartTransport w ha R S I J e)
    have hn' : ¬ (kmswStageDirectedMap w N).missing
        (J.toEquiv (selectedStageDartTransport w ha R S I J e)) := by
      intro hm
      exact hn ((J.missing_iff _).mp hm)
    change ¬ (kmswStage w N).present
      (J.toEquiv (selectedStageDartTransport w ha R S I J e)).1.val = false at hn'
    cases hp : (kmswStage w N).present
      (J.toEquiv (selectedStageDartTransport w ha R S I J e)).1.val <;> simp_all
  · simpa only [selectedStageDartTransport, Function.comp_apply,
      Equiv.apply_symm_apply, outerSucc_castDart] using ht

private theorem color_stageFace
    {x : XDP} {ℓ r n m N : ℕ} (w : ℕ → Fin 3)
    (S : KMSWMapRep ℓ r n) (hS : xdpLengthBase S.B x = m)
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (d : StageDart (kmswStage w N).nextEdge) (hd : d ∉ stageOuterWord w N) :
    selectedCutLeftColor S hS (J.toEquiv.symm ((kmswMap w N).faceSucc d)) =
      selectedCutLeftColor S hS (J.toEquiv.symm d) := by
  have hn : ¬ S.B.map.IsOuter (J.toEquiv.symm d) := by
    intro ho
    apply hd
    apply (color_stageOuter_iff w N d).mpr
    simpa only [Equiv.apply_symm_apply] using (J.outer_iff _).mpr ho
  have he := color_iso_faceSucc J (J.toEquiv.symm d)
  simp only [Equiv.apply_symm_apply] at he
  have he' := congrArg J.toEquiv.symm he
  simp only [Equiv.symm_apply_apply] at he'
  change S.B.map.faceSucc (J.toEquiv.symm d) =
    J.toEquiv.symm ((kmswMap w N).faceSucc d) at he'
  rw [← he']
  exact (selectedCutLeftColor_spec S hS).2.2.1 _ hn

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The later left coloring is constant on every previously created triangle. -/
theorem selectedCutLeftColor_stageTriangle
    {x : XDP} {ℓ r n m N : ℕ} (w : ℕ → Fin 3)
    (S : KMSWMapRep ℓ r n) (hS : xdpLengthBase S.B x = m)
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (j : TriangleCreationTime w) (hj : j.val < N) :
    let C := fun d => selectedCutLeftColor S hS (J.toEquiv.symm d)
    C (stageTriangleDart₁ w N j hj) = C (stageTriangleDart₂ w N j hj) ∧
      C (stageTriangleDart₂ w N j hj) = C (stageTriangleDart₃ w N j hj) := by
  have hf := stageTriangle_faceSucc3Cycle w (stageOuterWord_faceSucc w) j N hj
  have h₁ := color_stageFace w S hS J (stageTriangleDart₁ w N j hj)
    (stageTriangleDart_not_outer w N j hj _
      (by simp [stageTriangleDart₁, stageTriangleDartAt, stageTriangleDartList]))
  have h₂ := color_stageFace w S hS J (stageTriangleDart₂ w N j hj)
    (stageTriangleDart_not_outer w N j hj _
      (by simp [stageTriangleDart₂, stageTriangleDartAt, stageTriangleDartList]))
  rw [hf.1] at h₁
  rw [hf.2.1] at h₂
  exact ⟨h₁.symm, h₂.symm⟩

private theorem color_rank_step
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    (w : ℕ → Fin 3) (N : ℕ) {a : ℕ} (ha : a ≤ N)
    (J : DirectedMapWithMissingIso M (kmswStageDirectedMap w a))
    {u v : MapVertex M} (h : M.directedStep u v) :
    kmswStageRank w N (color_vertex w a J u).id <
      kmswStageRank w N (color_vertex w a J v).id := by
  obtain ⟨d, _, ht, rfl, rfl⟩ := h
  have hd := (J.tail_iff d).mpr ht
  change (kmswStage w a).present (J.toEquiv d).1.val = true ∧
    (J.toEquiv d).2 = false at hd
  change kmswStageRank w N (color_vertex w a J (dartTailVertex M d)).id <
    kmswStageRank w N (color_vertex w a J (dartHeadVertex M d)).id
  rw [color_vertex_tail, color_vertex_head, hd.2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hb := lt_of_lt_of_le (J.toEquiv d).1.isLt (kmswStage_nextEdge_mono w ha)
  have hs := kmswStageRank_strict w N (J.toEquiv d).1.val hb
  rw [(edge_endpoints_eq w hb).1, (edge_endpoints_eq w hb).2] at hs
  exact hs

private theorem color_rank_reach
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    (w : ℕ → Fin 3) (N : ℕ) {a : ℕ} (ha : a ≤ N)
    (J : DirectedMapWithMissingIso M (kmswStageDirectedMap w a))
    {u v : MapVertex M} (h : Relation.ReflTransGen M.directedStep u v) :
    kmswStageRank w N (color_vertex w a J u).id ≤
      kmswStageRank w N (color_vertex w a J v).id := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans (color_rank_step w N ha J hs).le

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every later geodesic dart allocated after the earlier stage starts at rank at least
that of the endpoint of the common prefix. -/
private theorem selectedStage_freshPathDart_rank
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv)
    (e : Fin S.dartCount) (he : e ∈ (selectedGeodesicOfLen S.B x hS).darts)
    (hfresh : (kmswStage w a).nextEdge ≤ (J.toEquiv e).1.val) :
    let Q := selectedGeodesicOfLen S.B x hS
    kmswStageRank w N
        (color_vertex w N J (Q.vertices.get ⟨m, by
          rw [Q.vertices_length]; have hm := hP.1; omega⟩)).id ≤
      kmswStageRank w N (color_vertex w N J (dartTailVertex S.B.map e)).id := by
  let Q := selectedGeodesicOfLen S.B x hS
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
  have him' : i < m' := lt_of_lt_of_eq hi Q.darts_length
  have hmi : m ≤ i := by
    by_contra hn
    have him : i < m := by omega
    obtain ⟨d, d', _, hd', hdd'⟩ := hP.2.1 i him
    have hget : Q.darts[i]? = some e := by rw [List.getElem?_eq_getElem hi, hie]
    have hde : d' = e := Option.some.inj (hd'.symm.trans hget)
    subst d'
    have hh := congrArg (fun z : StageDart (kmswStage w N).nextEdge => z.1.val) hdd'
    change (I.toEquiv d).1.val = (J.toEquiv e).1.val at hh
    have hb := (I.toEquiv d).1.isLt
    omega
  have hseg := color_rank_reach w N le_rfl J (color_path_segment Q m (i - m) (by omega))
  have hidx : m + (i - m) = i := by omega
  simp only [hidx] at hseg
  have hs := (Q.edge_step ⟨i, hi⟩).2.2.1
  have hget : Q.darts.get ⟨i, hi⟩ = e := hie
  rw [hget] at hs
  rw [hs] at hseg
  exact hseg

private noncomputable def color_stageEdge
    {x : XDP} {ℓ r n m N : ℕ} (w : ℕ → Fin 3)
    (S : KMSWMapRep ℓ r n) (hS : xdpLengthBase S.B x = m)
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (e : ℕ) (side : Bool) : Bool :=
  if h : e < (kmswStage w N).nextEdge then
    selectedCutLeftColor S hS (J.toEquiv.symm (⟨e, h⟩, side)) else false

private theorem color_UL_backward
    {x : XDP} {ℓ r n m a N : ℕ} (w : ℕ → Fin 3)
    (S : KMSWMapRep ℓ r n) (hS : xdpLengthBase S.B x = m)
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (b : ℚ)
    (hnew : ∀ k, a ≤ k → k < N →
      kmswStageRank w N (edgeWest w (kmswStage w k).nextEdge) < b →
      color_stageEdge w S hS J (kmswStage w k).nextEdge true =
        color_stageEdge w S hS J (kmswStage w k).nextEdge false) :
    ∀ k, a ≤ k → k ≤ N → ∀ e ∈ (kmswStage w k).UL,
      kmswStageRank w N (edgeWest w e) < b → color_stageEdge w S hS J e false = true := by
  let F := color_stageEdge w S hS J
  let ρ := kmswStageRank w N
  have hstrict (e : ℕ) (he : e < (kmswStage w N).nextEdge) :
      ρ (edgeWest w e) < ρ (edgeEast w e) := by
    have hs := kmswStageRank_strict w N e he
    rw [(edge_endpoints_eq w he).1, (edge_endpoints_eq w he).2] at hs
    exact hs
  have ht (j : TriangleCreationTime w) (hj : j.val < N) :
      F (stageTriangleDartTriple w j).1.1 (stageTriangleDartTriple w j).1.2 =
          F (stageTriangleDartTriple w j).2.1.1 (stageTriangleDartTriple w j).2.1.2 ∧
      F (stageTriangleDartTriple w j).2.1.1 (stageTriangleDartTriple w j).2.1.2 =
          F (stageTriangleDartTriple w j).2.2.1 (stageTriangleDartTriple w j).2.2.2 := by
    have hh := selectedCutLeftColor_stageTriangle w S hS J j hj
    have h₁ := stageTriangleDartList_lt w N j hj _
      (show (stageTriangleDartTriple w j).1 ∈ stageTriangleDartList w j by
        simp [stageTriangleDartList])
    have h₂ := stageTriangleDartList_lt w N j hj _
      (show (stageTriangleDartTriple w j).2.1 ∈ stageTriangleDartList w j by
        simp [stageTriangleDartList])
    have h₃ := stageTriangleDartList_lt w N j hj _
      (show (stageTriangleDartTriple w j).2.2 ∈ stageTriangleDartList w j by
        simp [stageTriangleDartList])
    simpa only [F, color_stageEdge, dite_eq_left h₁, dite_eq_left h₂, dite_eq_left h₃,
      stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃, stageTriangleDartAt]
      using hh
  have hnewF (k : ℕ) (hak : a ≤ k) (hkN : k < N)
      (hr : ρ (edgeWest w (kmswStage w k).nextEdge) < b) :
      F (kmswStage w k).nextEdge true = F (kmswStage w k).nextEdge false :=
    hnew k hak hkN hr
  have hind : ∀ d k, k + d = N → a ≤ k → ∀ e ∈ (kmswStage w k).UL,
      ρ (edgeWest w e) < b → F e false = true := by
    intro d
    induction d with
    | zero =>
      intro k hk _ e he _
      have hkN : k = N := by omega
      subst k
      have hb := stageRotation_UL_bound w N e he
      dsimp only [F, color_stageEdge]
      rw [dite_eq_left hb]
      apply (selectedCutLeftColor_spec S hS).1
      left
      apply (color_iso_ulDarts J _).mp
      rw [Equiv.apply_symm_apply]
      apply (kmswStageULDartsFinset_map_mem w N _).mp
      exact (kmswStageULDartsFinset_mem w N _).mpr ⟨rfl, he⟩
    | succ d ih =>
      intro k hk hak e he hrank
      have hkN : k < N := by omega
      have hnext : ∀ f ∈ (kmswStage w (k + 1)).UL,
          ρ (edgeWest w f) < b → F f false = true :=
        ih (k + 1) (by omega) (by omega)
      cases hc : kmswCodeStep (w k) with
      | down =>
        apply hnext e _ hrank
        cases hur : (kmswStage w k).UR <;>
          simp [kmswStage, kmswStep, hc, kmswStepOfStep, hur, State.addEdge, he]
      | left =>
        have h0 : w k = 0 := by
          by_contra h0
          simp only [kmswCodeStep, h0, ↓reduceIte] at hc
          split at hc <;> contradiction
        obtain ⟨xs, hxs⟩ := kmswStage_UL_last w k
        cases hl : (kmswStage w k).UL.dropLast.reverse with
        | nil =>
          have hempty : xs = [] := by simpa [hxs] using hl
          have heq : e = (kmswStage w k).active := by simpa [hxs, hempty] using he
          subst e
          have htri := ht ⟨k, Or.inl h0⟩ hkN
          simp only [stageTriangleDartTriple, h0, ↓reduceIte, hl] at htri
          have hside : ρ (edgeWest w (kmswStage w k).nextEdge) < b := by
            have hbound := stageTriangleDartList_lt w N ⟨k, Or.inl h0⟩ hkN
              ((kmswStage w k).nextEdge + 1, false)
              (by simp [stageTriangleDartList, stageTriangleDartTriple, h0, hl])
            have hlt := hstrict _ hbound
            have hend := edge_endpoints_eq w
              (show (kmswStage w k).nextEdge + 1 < (kmswStage w (k + 1)).nextEdge by
                simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
            have hends : edgeWest w ((kmswStage w k).nextEdge + 1) =
                edgeWest w (kmswStage w k).nextEdge ∧
                edgeEast w ((kmswStage w k).nextEdge + 1) =
                  edgeWest w (kmswStage w k).active := by
              have hn := edge_endpoints_eq w
                (show (kmswStage w k).nextEdge <
                    (kmswStage w (k + 1)).nextEdge by
                  simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge])
              have ha := (edge_endpoints_eq w (act_lt_nextEdge w (le_refl k))).1
              simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl,
                State.addEdge] at hend hn
              exact ⟨hend.1.symm.trans hn.1, hend.2.symm.trans ha⟩
            rw [hends.1, hends.2] at hlt
            exact hlt.trans hrank
          rw [htri.1, hnewF k hak hkN hside]
          apply hnext _ _ hside
          simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
        | cons f fs =>
          have hx : xs = fs.reverse ++ [f] := by
            have hh := congrArg List.reverse hl
            simpa [hxs] using hh
          have hecases : e ∈ fs.reverse ∨ e = f ∨ e = (kmswStage w k).active := by
            simpa [hxs, hx] using he
          rcases hecases with heold | hef | hea
          · apply hnext _ _ hrank
            simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge, heold]
          all_goals
            have htri := ht ⟨k, Or.inl h0⟩ hkN
            simp only [stageTriangleDartTriple, h0, ↓reduceIte, hl] at htri
            have hn := (edge_endpoints_eq w
              (show (kmswStage w k).nextEdge < (kmswStage w (k + 1)).nextEdge by
                simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge])).1
            have hfb : f < (kmswStage w k).nextEdge := stageRotation_UL_bound w k f
              (by simp [hxs, hx])
            have hfend := (edge_endpoints_eq w hfb).1
            have hw : edgeWest w (kmswStage w k).nextEdge = edgeWest w f := by
              simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge] at hn
              exact hn.symm.trans hfend
          · subst e
            have hs : ρ (edgeWest w (kmswStage w k).nextEdge) < b := by
              rw [hw]; exact hrank
            rw [htri.1, htri.2, hnewF k hak hkN hs]
            apply hnext _ _ hs
            simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
          · subst e
            have hchain := (kmswStage_boundary_chain_invariant w k).1.left_of_append
            change List.IsChain (fun f g => (kmswStage w k).east f =
              (kmswStage w k).west g) (kmswStage w k).UL at hchain
            rw [hxs, hx, List.append_assoc] at hchain
            have hfg := (List.isChain_append_cons_cons.mp hchain).2.1
            have hfe := (edge_endpoints_eq w hfb).2
            have hae := (edge_endpoints_eq w (act_lt_nextEdge w (le_refl k))).1
            have hs := hstrict f (lt_of_lt_of_le hfb (kmswStage_nextEdge_mono w hkN.le))
            have hfw : edgeEast w f = edgeWest w (kmswStage w k).active :=
              hfe.symm.trans (hfg.trans hae)
            rw [hfw] at hs
            have hb : ρ (edgeWest w (kmswStage w k).nextEdge) < b := by
              rw [hw]; exact hs.trans hrank
            rw [htri.2, hnewF k hak hkN hb]
            apply hnext _ _ hb
            simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
      | up =>
        have h1 : w k = 1 := by
          by_cases h0 : w k = 0
          · simp [kmswCodeStep, h0] at hc
          · by_contra h1
            simp [kmswCodeStep, h0, h1] at hc
        by_cases heact : e = (kmswStage w k).active
        · subst e
          have htri := ht ⟨k, Or.inr h1⟩ hkN
          have h0 : w k ≠ 0 := by rw [h1]; decide
          simp only [stageTriangleDartTriple, h0, ↓reduceIte] at htri
          have hn := (edge_endpoints_eq w
            (show (kmswStage w k).nextEdge < (kmswStage w (k + 1)).nextEdge by
              simp [kmswStage, kmswStep, hc, kmswStepOfStep, State.addEdge])).1
          have ha := (edge_endpoints_eq w (act_lt_nextEdge w (le_refl k))).1
          have hw : edgeWest w (kmswStage w k).nextEdge =
              edgeWest w (kmswStage w k).active := by
            simp [kmswStage, kmswStep, hc, kmswStepOfStep, State.addEdge] at hn
            exact hn.symm.trans ha
          have hb : ρ (edgeWest w (kmswStage w k).nextEdge) < b := by
            rw [hw]; exact hrank
          rw [htri.1, htri.2, hnewF k hak hkN hb]
          apply hnext _ _ hb
          simp [kmswStage, kmswStep, hc, kmswStepOfStep, State.addEdge]
        · apply hnext _ _ hrank
          have hd : e ∈ (kmswStage w k).UL.dropLast := by
            obtain ⟨xs, hxs⟩ := kmswStage_UL_last w k
            simpa [hxs, heact] using he
          simp [kmswStage, kmswStep, hc, kmswStepOfStep, State.addEdge, hd]
  intro k hak hk e he hr
  exact hind (N - k) k (by omega) hak e he hr

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every earlier left outer dart has the later left-region color, including darts
absorbed by subsequent triangle attachments. -/
theorem selectedStageLeftColor_leftOuterArc
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv) :
    ∀ e ∈ pathCutLeftOuterArc R.B, selectedStageLeftColor w ha R S hS I J e = true := by
  let P := selectedGeodesicOfLen R.B x hR
  let Q := selectedGeodesicOfLen S.B x hS
  have hmm' := hP.1
  let v := Q.vertices.get ⟨m, by rw [Q.vertices_length]; omega⟩
  let b := kmswStageRank w N (color_vertex w N J v).id
  have hnew (k : ℕ) (hak : a ≤ k) (hkN : k < N)
      (hr : kmswStageRank w N (edgeWest w (kmswStage w k).nextEdge) < b) :
      color_stageEdge w S hS J (kmswStage w k).nextEdge true =
        color_stageEdge w S hS J (kmswStage w k).nextEdge false := by
    by_cases hb : (kmswStage w k).nextEdge < (kmswStage w N).nextEdge
    · let d : Fin S.dartCount := J.toEquiv.symm (⟨(kmswStage w k).nextEdge, hb⟩, false)
      have hjd : J.toEquiv d = (⟨(kmswStage w k).nextEdge, hb⟩, false) :=
        J.toEquiv.apply_symm_apply _
      have hn : d ∉ pathCutSeamDarts S.B Q := by
        rintro (hd | hd)
        · have hfresh : (kmswStage w a).nextEdge ≤ (J.toEquiv d).1.val := by
            rw [hjd]; exact kmswStage_nextEdge_mono w hak
          have hle := selectedStage_freshPathDart_rank w ha R hR S hS I J fv gv hP
            d hd hfresh
          have hv := color_vertex_tail w N J d
          rw [hjd] at hv
          simp only [Bool.false_eq_true, ↓reduceIte] at hv
          rw [hv] at hle
          exact (not_lt_of_ge hle) hr
        · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
          have htail := (Q.edge_step i).2.1
          rw [hi] at htail
          have hs := (J.tail_iff _).mpr htail
          change (kmswStage w N).present _ = true ∧
            (J.toEquiv (S.B.map.edgeInv d)).2 = false at hs
          rw [J.edgeInv_comm, hjd] at hs
          exact Bool.noConfusion hs.2
      have hf := (selectedCutLeftColor_spec S hS).2.2.2 d hn
      have hrev : S.B.map.edgeInv d =
          J.toEquiv.symm (⟨(kmswStage w k).nextEdge, hb⟩, true) := by
        apply J.toEquiv.injective
        rw [J.edgeInv_comm, hjd, Equiv.apply_symm_apply]
        rfl
      rw [hrev] at hf
      simpa only [color_stageEdge, dite_eq_left hb] using hf
    · simp only [color_stageEdge, dite_eq_right hb]
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    have hsame : P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ =
        P.vertices.get ⟨m, by rw [P.vertices_length]; omega⟩ := by
      exact congrArg P.vertices.get (Fin.ext hm0.symm)
    exact bipolar_source_ne_sink R.B
      (P.start_vertex.symm.trans (hsame.trans P.end_vertex))
  obtain ⟨d, d', hd, hd', hdd'⟩ := hP.2.1 (m - 1) (by omega)
  have hdget : P.darts.get ⟨m - 1, by rw [P.darts_length]; omega⟩ = d := by
    exact Option.some.inj ((List.getElem?_eq_getElem
      (by rw [P.darts_length]; omega : m - 1 < P.darts.length)).symm.trans hd)
  have hdget' : Q.darts.get ⟨m - 1, by rw [Q.darts_length]; omega⟩ = d' := by
    exact Option.some.inj ((List.getElem?_eq_getElem
      (by rw [Q.darts_length]; omega : m - 1 < Q.darts.length)).symm.trans hd')
  have hτd : selectedStageDartTransport w ha R S I J d = d' := by
    apply J.toEquiv.injective
    simpa only [selectedStageDartTransport, Function.comp_apply,
      Equiv.apply_symm_apply] using hdd'
  have hsink : color_vertex w a I R.B.sink = color_vertex w N J v := by
    have hp := (P.edge_step ⟨m - 1, by rw [P.darts_length]; omega⟩).2.2.2
    have hq := (Q.edge_step ⟨m - 1, by rw [Q.darts_length]; omega⟩).2.2.2
    have hlast : m - 1 + 1 = m := by omega
    simp only [hlast, hdget, P.end_vertex] at hp
    simp only [hlast, hdget'] at hq
    change color_vertex w a I R.B.sink =
      color_vertex w N J (Q.vertices.get ⟨m, by rw [Q.vertices_length]; omega⟩)
    rw [hp, hq, ← hτd]
    exact (color_transport_endpoints w ha R S I J d).2
  intro e he
  have hi := (color_iso_ulDarts I e).mpr he
  have hside : (I.toEquiv e).2 = false := hi.2.1.2
  have hul := (kmswStageULDartsFinset_mem w a _).mp
    ((kmswStageULDartsFinset_map_mem w a _).mpr hi)
  have hrank : kmswStageRank w N (edgeWest w (I.toEquiv e).1.val) < b := by
    obtain ⟨k, H, _⟩ := exists_simple_sink_pathBase R.B (dartHeadVertex R.B.map e)
    have hle := color_rank_reach w N ha I (color_path_segment H 0 k (by omega))
    simp only [Nat.zero_add, H.start_vertex, H.end_vertex] at hle
    have hlt := color_rank_step w N ha I
      (show R.B.map.directedStep (dartTailVertex R.B.map e)
        (dartHeadVertex R.B.map e) from ⟨e, he.1, he.2.1, rfl, rfl⟩)
    have hh := hlt.trans_le hle
    rw [hsink, color_vertex_tail, hside] at hh
    exact hh
  have hh := color_UL_backward w S hS J b hnew a le_rfl ha _ hul.2 hrank
  have hb := lt_of_lt_of_le (I.toEquiv e).1.isLt (kmswStage_nextEdge_mono w ha)
  change selectedCutLeftColor S hS
    (J.toEquiv.symm (outerSucc_castDart (kmswStage_nextEdge_mono w ha) (I.toEquiv e))) =
      true
  simp only [outerSucc_castDart, hside]
  change selectedCutLeftColor S hS
    (J.toEquiv.symm (⟨(I.toEquiv e).1.val, hb⟩, false)) = true
  simpa only [color_stageEdge, dite_eq_left hb] using hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The common-stage transport preserves and reflects membership in the left closure. -/
theorem selectedStageDartTransport_leftDarts_iff
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv) :
    ∀ e, e ∈ pathCutLeftDarts R.B (selectedGeodesicOfLen R.B x hR) ↔
      selectedStageDartTransport w ha R S I J e ∈
        pathCutLeftDarts S.B (selectedGeodesicOfLen S.B x hS) := by
  let P := selectedGeodesicOfLen R.B x hR
  let c := selectedStageLeftColor w ha R S hS I J
  have hl : ∀ e ∈ pathCutLeftSeeds R.B P, c e = true := by
    rintro e (he | he)
    · exact selectedStageLeftColor_leftOuterArc w ha R hR S hS I J fv gv hP e he
    · exact selectedStageLeftColor_pathDart w ha R hR S hS I J fv gv hP e he
  have hr : ∀ e ∈ pathCutRightSeeds R.B P, c e = false := by
    rintro e (he | ⟨d, hd, rfl⟩)
    · exact selectedStageLeftColor_rightOuterArc w ha R S hS I J e he
    · exact selectedStageLeftColor_pathDart_flip w ha R hR S hS I J fv gv hP d hd
  have hf : ∀ e, ¬ R.B.map.IsOuter e → c (R.B.map.faceSucc e) = c e := by
    exact selectedStageLeftColor_faceSucc w ha R S hS I J
  have he := selectedStageLeftColor_edgeInv w ha R hR S hS I J fv gv hP
  intro e
  have hh := pathCutLeft_mem_iff_side_true_of_sideColoring R.B P c hl hr hf he e
  simpa only [c, selectedStageLeftColor, selectedCutLeftColor, decide_eq_true_eq] using hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The common-stage transport preserves and reflects the edge-closed left half. -/
theorem selectedStageDartTransport_leftHalfDarts_iff
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv) :
    ∀ e, e ∈ pathCutLeftHalfDarts R.B (selectedGeodesicOfLen R.B x hR) ↔
      selectedStageDartTransport w ha R S I J e ∈
        pathCutLeftHalfDarts S.B (selectedGeodesicOfLen S.B x hS) := by
  intro e
  apply or_congr
  · exact selectedStageDartTransport_leftDarts_iff w ha R hR S hS I J fv gv hP e
  · exact ⟨selectedStageDartTransport_seam w ha R hR S hS I J fv gv hP e,
      selectedStageDartTransport_seam_reflect w ha R hR S hS I J fv gv hP e⟩

private theorem color_rightHalf_iff
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (e : D) :
    e ∈ pathCutRightHalfDarts B P ↔
      e ∉ pathCutLeftHalfDarts B P ∨ e ∈ pathCutSeamDarts B P := by
  constructor
  · intro hr
    by_cases hl : e ∈ pathCutLeftHalfDarts B P
    · right
      have hh : e ∈ pathCutLeftHalfDarts B P ∩ pathCutRightHalfDarts B P := ⟨hl, hr⟩
      rw [pathCut_halves_inter_eq_seam] at hh
      exact hh
    · exact Or.inl hl
  · rintro (hn | hs)
    · exact (pathCut_halves_cover B P e).resolve_left hn
    · exact Or.inr hs

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The common-stage transport preserves and reflects the edge-closed right half. -/
theorem selectedStageDartTransport_rightHalfDarts_iff
    {x : XDP} {ℓ r n m ℓ' r' n' m' a N : ℕ} {β : Type*}
    (w : ℕ → Fin 3) (ha : a ≤ N)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (S : KMSWMapRep ℓ' r' n') (hS : xdpLengthBase S.B x = m')
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w a))
    (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N))
    (fv : MapVertex R.B.map → β) (gv : MapVertex S.B.map → β)
    (hP : CommonSelectedPrefix R hR S hS
      (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv fv gv) :
    ∀ e, e ∈ pathCutRightHalfDarts R.B (selectedGeodesicOfLen R.B x hR) ↔
      selectedStageDartTransport w ha R S I J e ∈
        pathCutRightHalfDarts S.B (selectedGeodesicOfLen S.B x hS) := by
  intro e
  rw [color_rightHalf_iff, color_rightHalf_iff]
  apply or_congr
  · exact not_congr
      (selectedStageDartTransport_leftHalfDarts_iff w ha R hR S hS I J fv gv hP e)
  · exact ⟨selectedStageDartTransport_seam w ha R hR S hS I J fv gv hP e,
      selectedStageDartTransport_seam_reflect w ha R hR S hS I J fv gv hP e⟩

/- In the common-prefix context, with local abbreviations

  let P := selectedGeodesicOfLen R.B x hR
  let Q := selectedGeodesicOfLen S.B x hS
  let τ := selectedStageDartTransport w ha R S I J
  let c := selectedStageLeftColor w ha R S hS I J

the following transport statements are proved above:

  ∀ e ∈ pathCutLeftOuterArc R.B, c e = true
  ∀ e, e ∈ pathCutLeftDarts R.B P ↔ τ e ∈ pathCutLeftDarts S.B Q
  ∀ e, e ∈ pathCutLeftHalfDarts R.B P ↔ τ e ∈ pathCutLeftHalfDarts S.B Q
  ∀ e, e ∈ pathCutRightHalfDarts R.B P ↔ τ e ∈ pathCutRightHalfDarts S.B Q

The color uses the left closure before adjoining both seam darts. The half
carrier statements then follow from exact seam transport and the fact that
both closed halves cover the dart carrier and intersect exactly on the seam. -/

end DirectedDistances.PaperProofs.Section4
