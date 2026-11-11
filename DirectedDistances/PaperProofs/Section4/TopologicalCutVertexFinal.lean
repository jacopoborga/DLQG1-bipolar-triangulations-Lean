module

public import DirectedDistances.PaperProofs.Section4.TopologicalCutVertexSource
public import DirectedDistances.KMSW.KMSWConstructedRealizationProof

/-! # Unconditional source interface for topological cut vertices

Providers toward `def-cut-vertex`, `prop-cut-vertex`, `lem-cut-equiv` and Lemma 4.9 A5
`TopologicalCutVertexSource` were conditional on the n308 realization theorem; it is now
proved (`KMSW.kmswConstructedPlaneRealization`), and the same proofs are repeated here with
that theorem in place of the hypothesis. These are providers only: no paper anchor is
installed or counted here. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- The literal constructed-witness cut-vertex predicate agrees with the combinatorial
paper result. -/
theorem sourceCutVertex_iff_uiqbotCutVertex_final
    (w : ℕ → Fin 3) (hfin : DrawingFiniteIncidence w)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (v : ℕ) :
    sourceCutVertex w v ↔ uiqbotCutVertex w v := by
  constructor
  · exact sourceCutVertex_forward w v htrans hR hL0
  · intro hcut
    obtain ⟨Q, hstages, P, hpos, harc, U, hUnbounded, hUnique, hClass⟩ :=
      kmswConstructedPlaneRealization w hfin htrans hR hL0
    have hBuilt : Built w hfin P U :=
      ⟨⟨Q, hstages, hpos, harc⟩, hUnbounded, hUnique, hClass⟩
    have htop := (topBoundaryVertices_iff_uiqbotCutVertex w htrans hR hL0 P U
      hClass v).mpr hcut
    exact ⟨hfin, P, U, hBuilt, htop.1, htop.2⟩

/-- Unconditional provider for Definition 4.2's characterization (`def-cut-vertex`, -/
theorem cutVertex_characterization_final :
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
        sourceCutVertex_iff_uiqbotCutVertex_final w hfinDelete htrans hR hL0 v
      _ ↔ mapCutVertex w hfinDelete v :=
        uiqbotCutVertex_iff_mapCutVertex w hfinDelete htrans hR hL0 v
      _ ↔ v = 0 ∨ DeletingDisconnects w v := by
        simpa only [hrootZero] using hdeleteIff v
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

/-- Unconditional provider for Proposition 4.3 (`prop-cut-vertex`, -/
theorem cut_vertex_infinite_final :
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
  have hiff := sourceCutVertex_iff_uiqbotCutVertex_final w hfin htrans hR hL0
  refine ⟨w, ⟨hwp, ?_⟩, ?_⟩
  · exact (hinfinite w hwp).mono (fun v hv => (hiff v).mpr hv)
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

/-- Unconditional provider for Lemma 4.8 (`lem-cut-equiv`, -/
theorem cut_equiv_final :
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
  have hiff := sourceCutVertex_iff_uiqbotCutVertex_final w hfin htrans hR hL0
  refine ⟨w, ⟨hwp, ?_⟩, ?_⟩
  · intro n
    simpa only [hiff] using hequiv w hwp n
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

/-- Unconditional provider for Lemma 4.9 A5 (`lem-renewal`, -/
theorem renewalTime_cutVertex_rank_final :
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
  have hiff := sourceCutVertex_iff_uiqbotCutVertex_final w hfin htrans hR hL0
  refine ⟨w, ⟨hwp, ?_⟩, ?_⟩
  · intro m t
    simpa only [hiff] using hrank w hwp m t
  · intro w' hw'
    exact integrateCodes_injective (hw'.1.trans hwp.symm)

end DirectedDistances.PaperProofs.Section4
