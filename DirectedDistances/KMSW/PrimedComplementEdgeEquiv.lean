module

public import DirectedDistances.KMSW.PrimedComplementCoverageCrossing

/-! # Primed present edges and the never-reachable present-edge complement

The coherent limit edge map is injective on locally present edges. Together
with complement coverage, this gives an equivalence onto the full global
present-edge complement, preserving ordered endpoints through the limit
vertex map. These are edge-only helpers, not a proof of Lemma 5.13. -/

public section
namespace DirectedDistances.KMSW

/-- d143 item P2* (edge equivalence onto the never-reachable present-edge complement);
primedStageTime follows the implemented interval blocks, not a ruling on positive-time counting convention;
C18 root convention; Q1–Q3 not used (no vertex or face region claims);
not the paper result. The limit edge map is injective on present primed edges. -/
theorem primedLimitEdgeMap_injective_on (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective
      (fun e : {e : ℕ // PrimedEdgePresent w h e} => primedLimitEdgeMap w h e.1) := by
  intro e f hef
  obtain ⟨m, hm, _⟩ := e.2
  obtain ⟨n, hn, _⟩ := f.2
  exact Subtype.ext
    ((primedLimit_maps_injective_on_allocated w h).1 ⟨m, hm⟩ ⟨n, hn⟩ hef)

/-- d143 item P2* (edge equivalence onto the never-reachable present-edge complement);
primedStageTime follows the implemented interval blocks, not a ruling on positive-time counting convention;
C18 root convention; Q1–Q3 not used (no vertex or face region claims);
not the paper result. Present primed edges correspond bijectively to all globally
present edges outside every root-reachable present-edge set. -/
@[expose] noncomputable def primedComplementEdgeEquiv (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    {e : ℕ // PrimedEdgePresent w h e} ≃
      {e' : ℕ // EdgePresent w e' ∧ ∀ n, e' ∉ stageReachablePresentEdges w n} :=
  Equiv.ofBijective
    (fun e =>
      let hd := primedLimitEdge_data w h e.2
      ⟨primedLimitEdgeMap w h e.1, hd.1, hd.2.1⟩)
    (by
      constructor
      · intro e f hef
        exact primedLimitEdgeMap_injective_on w h (congrArg Subtype.val hef)
      · rintro ⟨e', hp, hnever⟩
        obtain ⟨e, he, heq⟩ := primedLimitEdgeComplement w h e' hp hnever
        exact ⟨⟨e, he⟩, Subtype.ext heq⟩)

/-- d143 item P2* (edge equivalence onto the never-reachable present-edge complement);
primedStageTime follows the implemented interval blocks, not a ruling on positive-time counting convention;
C18 root convention; Q1–Q3 not used (no vertex or face region claims);
not the paper result. The equivalence acts on edge IDs by the limit edge map. -/
@[simp] theorem primedComplementEdgeEquiv_apply_val (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : {e : ℕ // PrimedEdgePresent w h e}) :
    (primedComplementEdgeEquiv w h e).1 = primedLimitEdgeMap w h e.1 := rfl

/-- d143 item P2* (edge equivalence onto the never-reachable present-edge complement);
primedStageTime follows the implemented interval blocks, not a ruling on positive-time counting convention;
C18 root convention; Q1–Q3 not used (no vertex or face region claims);
not the paper result. Ordered west/east endpoints commute with the same limit
vertex map used by primedLimitIncidence; no vertex-region equivalence is asserted. -/
theorem primedComplementEdgeEquiv_endpoints (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : {e : ℕ // PrimedEdgePresent w h e}) :
    edgeWest w (primedComplementEdgeEquiv w h e).1 =
      primedLimitVertexMap w h (edgeWest (primedCode (primedSimInput w) h) e.1) ∧
    edgeEast w (primedComplementEdgeEquiv w h e).1 =
      primedLimitVertexMap w h (edgeEast (primedCode (primedSimInput w) h) e.1) :=
  (primedLimitEdge_data w h e.2).2.2

end DirectedDistances.KMSW
