module

public import DirectedDistances.KMSW.PrimedImageLimit
public import DirectedDistances.KMSW.HatFaceIso

/-! # Primed edge-triple image helper

not counted. The local carrier follows the stagewise primed reading. The
current simulation records global triangle incidence up to equality of edge
multisets; this module does not identify the resulting edge-triple order or
claim coverage of the whole present-edge complement. -/

public section
namespace DirectedDistances.KMSW

/-- Primed local triangles recorded at some missing-root stage, for the
P2 helper; not counted. -/
@[expose] def PrimedLocalTri (w : ℕ → Fin 3) (h : HasFlowLineHits w) :=
  {t : ℕ × ℕ × ℕ // ∃ m, t ∈
    (kmswMissingRootStage (primedCode (primedSimInput w) h) m).triangles}

end DirectedDistances.KMSW
