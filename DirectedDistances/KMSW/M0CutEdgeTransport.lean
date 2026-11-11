module

public import DirectedDistances.KMSW.KMSWWholePlaneFaces
public import DirectedDistances.KMSW.WholePlaneRightBoundaryRot
public import DirectedDistances.KMSW.WholePlaneDrawingCombinatorics
public import DirectedDistances.KMSW.WholePlaneRootedMapFields
public import DirectedDistances.KMSW.KMSWFutureMapCarrier

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap Quiver

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
Presence transport copies the whole-plane colimit lemma's chosen-endpoint
freshness condition exactly. -/
theorem m0Cut_edgePresent_iff_of_fresh (W : ℤ → Fin 3) (e : ℕ) (b : Bool)
    (hf : ∀ M (h0M : 0 ≤ M), wholePlaneFresh W 0 M h0M
      (if b then edgeEast (shiftedStream W 0) e
        else edgeWest (shiftedStream W 0) e)) :
    EdgePresent (shiftedStream W 0) e ↔
      wholePlaneEdgePresent W (wholePlaneEdgeι W 0 e) := by
  exact (wholePlaneEdgePresent_ι_of_fresh W 0 e b hf).symm

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
Missingness has the same exact chosen-endpoint freshness condition. -/
theorem m0Cut_edgeMissing_iff_of_fresh (W : ℤ → Fin 3) (e : ℕ) (b : Bool)
    (hf : ∀ M (h0M : 0 ≤ M), wholePlaneFresh W 0 M h0M
      (if b then edgeEast (shiftedStream W 0) e
        else edgeWest (shiftedStream W 0) e)) :
    ¬ EdgePresent (shiftedStream W 0) e ↔
      ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W 0 e) := by
  exact not_congr (m0Cut_edgePresent_iff_of_fresh W e b hf)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
The west endpoint is transported by the run-zero edge inclusion. -/
theorem m0Cut_edgeWest (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgeWest W (wholePlaneEdgeι W 0 e) =
      wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) e) :=
  wholePlaneEdgeWest_ι W 0 e

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
The east endpoint is transported by the run-zero edge inclusion. -/
theorem m0Cut_edgeEast (W : ℤ → Fin 3) (e : ℕ) :
    wholePlaneEdgeEast W (wholePlaneEdgeι W 0 e) =
      wholePlaneVertexι W 0 (edgeEast (shiftedStream W 0) e) :=
  wholePlaneEdgeEast_ι W 0 e

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
Run-zero edge inclusion is injective. -/
theorem m0Cut_edgeι_injective (W : ℤ → Fin 3) :
    Function.Injective (wholePlaneEdgeι W 0) :=
  wholePlaneEdgeι_injective W 0

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
The run-zero root edge has neither endpoint fresh at the reflexive transition. -/
theorem m0Cut_root_edge_not_fresh_at_zero (W : ℤ → Fin 3) :
    ¬ wholePlaneFresh W 0 0 le_rfl (edgeWest (shiftedStream W 0) 0) ∧
      ¬ wholePlaneFresh W 0 0 le_rfl (edgeEast (shiftedStream W 0) 0) := by
  simp [wholePlaneFresh, wholePlaneVertexTrans, kmswWindowVertexMapInf_zero_start,
    edgeWest, edgeEast, kmswStage, kmswInit]

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
The image of each one-sided directed step is a present tail dart in the colimit;
the one-sided step relation is exactly its arrow-carrier condition. -/
theorem m0Cut_directedStep_iff (W : ℤ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage (shiftedStream W 0) n).nextEdge ∧
      ((kmswStage (shiftedStream W 0) n).west e = v ∨
        (kmswStage (shiftedStream W 0) n).east e = v)}.Finite)
    (u v : RootedLocallyFiniteVertex (ℕ × Bool)
      (kmswInfRot (shiftedStream W 0) hfin)) :
    rootedLocallyFiniteDirectedStep (kmswInfRot (shiftedStream W 0) hfin)
      futureMapEdgeInv
      (futureMapMissing (shiftedStream W 0))
      (futureMapTail (shiftedStream W 0)) u v ↔
    ∃ d : FutureMapArrowDart (shiftedStream W 0) hfin u v,
      wholePlaneDartTail W (wholePlaneDartι W 0 d.val) := by
  constructor
  · intro hstep
    obtain ⟨d⟩ := (futureMap_directedStep_iff (shiftedStream W 0) hfin u v).mp hstep
    refine ⟨d, ?_⟩
    rcases d with ⟨⟨e, b⟩, hmissing, htail, hu, hv⟩
    rcases htail with ⟨hb, hp⟩
    have hp' : EdgePresent (shiftedStream W 0) e := hp
    have hb' : b = false := by simpa using hb
    change ¬ (b = true) ∧ wholePlaneEdgePresent W (wholePlaneEdgeι W 0 e)
    constructor
    · simp [hb']
    · exact wholePlaneEdgePresent_ι_of_run_present W 0 e hp'
  · rintro ⟨d, _⟩
    exact (futureMap_directedStep_iff (shiftedStream W 0) hfin u v).mpr ⟨d⟩

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result. Source:
The run-zero dart map is injective on each one-sided arrow carrier. -/
theorem m0Cut_futureMapArrowDart_injective (W : ℤ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage (shiftedStream W 0) n).nextEdge ∧
      ((kmswStage (shiftedStream W 0) n).west e = v ∨
        (kmswStage (shiftedStream W 0) n).east e = v)}.Finite)
    (u v : RootedLocallyFiniteVertex (ℕ × Bool)
      (kmswInfRot (shiftedStream W 0) hfin)) :
    Function.Injective (fun d : FutureMapArrowDart (shiftedStream W 0) hfin u v =>
      wholePlaneDartι W 0 d.val) := by
  intro d₁ d₂ h
  apply Subtype.ext
  apply Prod.ext
  · apply wholePlaneEdgeι_injective W 0
    exact congrArg Prod.fst h
  · have h₁ : d₁.val.2 = false := d₁.property.2.1.1
    have h₂ : d₂.val.2 = false := d₂.property.2.1.1
    exact h₁.trans h₂.symm

end DirectedDistances.KMSW
