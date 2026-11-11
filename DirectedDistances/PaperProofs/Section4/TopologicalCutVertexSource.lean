module

public import DirectedDistances.KMSW.ConstructedBoundaryVertices
public import DirectedDistances.KMSW.LimitVertexDeletion
public import DirectedDistances.PaperProofs.Section4.CutVertexSource

/- # Conditional source interface for topological cut vertices

These are conditional helpers toward `def-cut-vertex`, `prop-cut-vertex`,
realization theorem. They are not paper results and will be instantiated, never
counted, until `HReal` is a theorem. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Finite incidence for a code, as used by the constructed plane-realization -/
abbrev DrawingFiniteIncidence (w : ℕ → Fin 3) :=
  ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite

 
abbrev Drawing (w : ℕ → Fin 3) (hfin : DrawingFiniteIncidence w) :=
  PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot w hfin) (kmswLimitDartVertex w)

/-- Stage compatibility, unique unbounded face, and external-dart classification -/
@[expose] def Built (w : ℕ → Fin 3) (hfin : DrawingFiniteIncidence w)
    (P : Drawing w hfin) (U : P.Face) : Prop :=
  (∃ Q : ∀ n, StageDrawing w n,
    (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
    (∀ n v, P.pos v.val = (Q n).pos v) ∧
    (∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d)) ∧
  P.IsUnbounded U ∧
  (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
  (∀ d, P.dartBorders d U ↔ limitExternalDart w d)

/-- Left-boundary endpoint membership for a classified constructed drawing -/
@[expose] def TopLeft (w : ℕ → Fin 3) {hfin : DrawingFiniteIncidence w}
    (P : Drawing w hfin) (U : P.Face) (v : ℕ) : Prop :=
  ∃ e, P.dartBorders (e, false) U ∧
    (edgeWest w e = v ∨ edgeEast w e = v)

/-- Right-boundary endpoint membership for a classified constructed drawing -/
@[expose] def TopRight (w : ℕ → Fin 3) {hfin : DrawingFiniteIncidence w}
    (P : Drawing w hfin) (U : P.Face) (v : ℕ) : Prop :=
  ∃ e, P.dartBorders (e, true) U ∧
    (edgeWest w e = v ∨ edgeEast w e = v)

/-- The topological predicate witnessed by a constructed plane realization -/
@[expose] def sourceCutVertex (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  ∃ hfin : DrawingFiniteIncidence w, ∃ P : Drawing w hfin, ∃ U : P.Face,
    Built w hfin P U ∧ TopLeft w P U v ∧ TopRight w P U v

/- Conditional helper toward `def-cut-vertex`, `prop-cut-vertex`,
will not count until that theorem is proved. -/
def HReal : Prop := ∀ (w : ℕ → Fin 3) (hfin : DrawingFiniteIncidence w)
  (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
  (hL0 : ∀ j, 0 ≤ L w j),
    KMSWConstructedPlaneRealizationStatement w hfin htrans hR hL0

/-- The hreal-free forward implication: every constructed witness has both
combinatorial boundary memberships (`def-cut-vertex`, -/
theorem sourceCutVertex_forward (w : ℕ → Fin 3) (v : ℕ)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) :
    sourceCutVertex w v → uiqbotCutVertex w v := by
  rintro ⟨hfin, P, U, hBuilt, hleft, hright⟩
  exact (topBoundaryVertices_iff_uiqbotCutVertex w htrans hR hL0 P U
    hBuilt.2.2.2 v).mp ⟨hleft, hright⟩

/-- Under `HReal`, the literal constructed-witness predicate agrees with the
combinatorial boundary predicate (`def-cut-vertex`,
n308 realization theorem and is not itself a paper result. -/
theorem sourceCutVertex_iff_uiqbotCutVertex (hreal : HReal)
    (w : ℕ → Fin 3) (hfin : DrawingFiniteIncidence w)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (v : ℕ) :
    sourceCutVertex w v ↔ uiqbotCutVertex w v := by
  constructor
  · exact sourceCutVertex_forward w v htrans hR hL0
  · intro hcut
    obtain ⟨Q, hstages, P, hpos, harc, U, hUnbounded, hUnique, hClass⟩ :=
      hreal w hfin htrans hR hL0
    have hBuilt : Built w hfin P U :=
      ⟨⟨Q, hstages, hpos, harc⟩, hUnbounded, hUnique, hClass⟩
    have htop := (topBoundaryVertices_iff_uiqbotCutVertex w htrans hR hL0 P U
      hClass v).mpr hcut
    exact ⟨hfin, P, U, hBuilt, htop.1, htop.2⟩

/- Conditional Definition 4.2 helper toward `def-cut-vertex`
is proved. -/
theorem cutVertex_characterization (hreal : HReal) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧ edgeWest w 0 = 0 ∧
        ∀ v, sourceCutVertex w v ↔ v = 0 ∨ DeletingDisconnects w v := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    conditionedVectorPathLaw_ae_mapCutVertex_iff_source_or_deletingDisconnects]
      with p hcarrier hregular hdelete
  obtain ⟨w, ⟨hwp, hroot⟩, _⟩ := hcarrier
  obtain ⟨wreg, hwpreg, hfin, htrans, hR, hL0, _, _⟩ := hregular
  have hcode : wreg = w := integrateCodes_injective (hwpreg.trans hwp.symm)
  subst wreg
  obtain ⟨_, hdelete⟩ := hdelete
  obtain ⟨hfinDelete, _, hdeleteIff⟩ := hdelete w hwp
  have hrootZero : edgeWest w 0 = 0 := hroot.1.1
  refine ⟨w, ⟨hwp, hrootZero, ?_⟩, ?_⟩
  · intro v
    calc
      sourceCutVertex w v ↔ uiqbotCutVertex w v :=
        sourceCutVertex_iff_uiqbotCutVertex hreal w hfinDelete htrans hR hL0 v
      _ ↔ mapCutVertex w hfinDelete v :=
        uiqbotCutVertex_iff_mapCutVertex w hfinDelete htrans hR hL0 v
      _ ↔ v = 0 ∨ DeletingDisconnects w v := by
        simpa only [hrootZero] using hdeleteIff v
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

/-- Conditional Proposition 4.3 helper (`prop-cut-vertex`,
n308 realization theorem `HReal`; this is not a paper result until it is proved. -/
theorem cut_vertex_infinite (hreal : HReal) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        {v : ℕ | sourceCutVertex w v}.Infinite := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    source_cut_vertex_infinite] with p hcarrier hregular hsource
  obtain ⟨w, ⟨hwp, _⟩, _⟩ := hcarrier
  obtain ⟨wreg, hwpreg, hfin, htrans, hR, hL0, _, _⟩ := hregular
  have hcode : wreg = w := integrateCodes_injective (hwpreg.trans hwp.symm)
  subst wreg
  obtain ⟨_, hinfinite⟩ := hsource
  have hiff := sourceCutVertex_iff_uiqbotCutVertex hreal w hfin htrans hR hL0
  refine ⟨w, ⟨hwp, ?_⟩, ?_⟩
  · exact (hinfinite w hwp).mono (fun v hv => (hiff v).mpr hv)
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

/-- Conditional Lemma 4.8 helper (`lem-cut-equiv`,
n308 realization theorem `HReal`; this is not a paper result until it is proved. -/
theorem cut_equiv (hreal : HReal) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        ∀ n : ℕ,
          (sourceCutVertex w (activeInitial w n) ∧
            ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
          ((∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
            ∀ j, n ≤ j → (p n).1 ≤ (p j).1) := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    source_cut_equiv] with p hcarrier hregular hsource
  obtain ⟨w, ⟨hwp, _⟩, _⟩ := hcarrier
  obtain ⟨wreg, hwpreg, hfin, htrans, hR, hL0, _, _⟩ := hregular
  have hcode : wreg = w := integrateCodes_injective (hwpreg.trans hwp.symm)
  subst wreg
  obtain ⟨_, hequiv⟩ := hsource
  have hiff := sourceCutVertex_iff_uiqbotCutVertex hreal w hfin htrans hR hL0
  refine ⟨w, ⟨hwp, ?_⟩, ?_⟩
  · intro n
    simpa only [hiff] using hequiv w hwp n
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

/-- Conditional Lemma 4.9 A5 helper (`lem-renewal`,
n308 realization theorem `HReal`; this is not a paper result until it is proved.
The positive-success rank keeps rank zero and the value `∞`. -/
theorem renewalTime_cutVertex_rank (hreal : HReal) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        ∀ (m : ℕ) (t : ℕ∞),
          Paper.Section4.renewalTime m p = t ↔
            IsPositiveSuccessTime
              (fun n => sourceCutVertex w (activeInitial w n) ∧
                ∀ j < n, activeInitial w j ≠ activeInitial w n) m t := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    source_renewalTime_cutVertex_rank] with p hcarrier hregular hsource
  obtain ⟨w, ⟨hwp, _⟩, _⟩ := hcarrier
  obtain ⟨wreg, hwpreg, hfin, htrans, hR, hL0, _, _⟩ := hregular
  have hcode : wreg = w := integrateCodes_injective (hwpreg.trans hwp.symm)
  subst wreg
  obtain ⟨_, hrank⟩ := hsource
  have hiff := sourceCutVertex_iff_uiqbotCutVertex hreal w hfin htrans hR hL0
  refine ⟨w, ⟨hwp, ?_⟩, ?_⟩
  · intro m t
    simpa only [hiff] using hrank w hwp m t
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

end DirectedDistances.PaperProofs.Section4

