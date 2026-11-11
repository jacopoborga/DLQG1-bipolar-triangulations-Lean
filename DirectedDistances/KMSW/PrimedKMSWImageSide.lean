module

public import DirectedDistances.KMSW.PrimedRotInducedOriented
public import DirectedDistances.KMSW.PrimedImageLimit
public import DirectedDistances.KMSW.PrimedInducedEmbedding
public import DirectedDistances.KMSW.PrimedFaceImage
import DirectedDistances.KMSW.PrimedInitialCut
import DirectedDistances.KMSW.HatTriangleSim

/-! # Primed KMSW image-side helper

not counted as Lemma 5.13. For the primed exploration `K̂′` built from
`primedCode` under C13, this records its limit-map image on allocated
vertices and locally present edges, the ordered incidence and unreachable
properties of that edge image, stage compatibility, the oriented dart-map
properties, multiset-level triangle images, and positive-stage rooted induced
embeddings with first-return rotation. Present edges are never reversed;
`primedDartMapOriented` may reverse locally missing edges.

This does not claim coverage of the present-edge complement or the cut
completion (G1 cut-completion and G2 present-edge coverage), identification
of permanently missing edges with β₀ or a resolution of the retained-β₀
vertex reading (G3 β₀ identification and G4 retained-β₀ vertices / Q2), or
the stage-zero root correspondence (G5 initial root / Q3). It does not claim
ordered face triples or the face identification (Q1), and
remaining G1–G6, Q1–Q3, and positive-time counting convention gates are open. This helper does not resolve
any source discrepancy or count toward Lemma 5.13. -/

public section
namespace DirectedDistances.KMSW



















theorem primedKMSW_imageSide (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (∃ (V : PrimedAllocatedVertex w h ≃ PrimedLimitVertexImage w h)
        (E : {e : ℕ // PrimedEdgePresent w h e} ≃ PrimedLimitEdgeImage w h),
        (∀ a, (V a).1 = primedLimitVertexMap w h a.1) ∧
        (∀ e, (E e).1 = primedLimitEdgeMap w h e.1) ∧
        (∀ e : {e : ℕ // PrimedEdgePresent w h e},
          edgeWest w (E e).1 =
            primedLimitVertexMap w h
              (edgeWest (primedCode (primedSimInput w) h) e.1) ∧
          edgeEast w (E e).1 =
            primedLimitVertexMap w h
              (edgeEast (primedCode (primedSimInput w) h) e.1)) ∧
        (∀ e n, (E e).1 ∉ stageReachablePresentEdges w n)) ∧
    (∀ m d, primedDartMapOriented w h (m + 1)
        (outerSucc_castDart
          (primedLocal_nextEdge_succ_le (primedCode (primedSimInput w) h) m) d) =
      outerSucc_castDart (kmswStage_nextEdge_mono w
        (primedStageTime_succ_le w h m))
        (primedDartMapOriented w h m d)) ∧
    ((∀ m a, a <
        (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge →
        primedLimitEdgeMap w h a = primedAllEdgeMap w h m a) ∧
     (∀ m v, v <
        (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextVertex →
        primedLimitVertexMap w h v = primedAllVertexMap w h m v)) ∧
    (∀ m,
      Function.Injective (primedDartMapOriented w h m) ∧
      (∀ d, primedDartMapOriented w h m
          (edgeFlip (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge d) =
        edgeFlip (kmswStage w (primedStageTime w h m)).nextEdge
          (primedDartMapOriented w h m d)) ∧
      (∀ d, stageEndpoint (kmswStage w (primedStageTime w h m))
          (primedDartMapOriented w h m d) =
        primedAllVertexMap w h m
          (stageEndpoint (kmswMissingRootStage (primedCode (primedSimInput w) h) m) d))) ∧
    (∀ m e,
      primedSideFlip w h m e = true →
        (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e.val = false) ∧
    (∀ t : PrimedLocalTri w h, ∃ n, ∃ t' ∈ (kmswStage w n).triangles,
      ({t'.1, t'.2.1, t'.2.2} : Multiset ℕ) =
        {primedLimitEdgeMap w h t.1.1,
          primedLimitEdgeMap w h t.1.2.1,
          primedLimitEdgeMap w h t.1.2.2}) ∧
    (∀ m (hm : 1 ≤ m),
      ∃ ι : RootedInducedEmbedding (primedRootedStage w h m hm)
          (kmswRootedStage w (primedStageTime w h m)),
        ι.dartMap = primedDartMapOriented w h m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨V, E, hV, hE, hInc⟩ := primedLimitIncidence w h
    refine ⟨V, E, hV, hE, hInc, ?_⟩
    intro e n
    exact (E e).property.2.1 n
  · intro m d
    exact primedDartMapOriented_compatible w h m d
  · exact ⟨(fun m a ha => (primedLimit_maps_eq_of_allocated w h m).1 a ha),
      (fun m v hv => (primedLimit_maps_eq_of_allocated w h m).2 v hv)⟩
  · intro m
    exact ⟨primedDartMapOriented_injective w h m,
      primedDartMapOriented_flip_comm w h m,
      primedDartMapOriented_endpoint w h m⟩
  · exact fun m e he => primedSideFlip_true_missing w h m e he
  · intro t
    obtain ⟨m, ht⟩ := t.property
    let u := primedCode (primedSimInput w) h
    let sh := kmswMissingRootStage u m
    have ht' : t.1 ∈ sh.triangles := ht
    have htri : ∃ n, ∃ t' ∈ (kmswStage w n).triangles,
        ({primedAllEdgeMap w h m t.1.1,
          primedAllEdgeMap w h m t.1.2.1,
          primedAllEdgeMap w h m t.1.2.2} : Multiset ℕ) =
          {t'.1, t'.2.1, t'.2.2} := by
      by_cases hm : m = 0
      · subst m
        have hsim := (primedAll_sim_zero w h).2.1
        obtain ⟨x, y, z, hxyz, hset⟩ := hsim.triangle_incidence _ _ _ ht'
        exact ⟨primedStageTime w h 0, (x, y, z), hxyz, hset⟩
      · have hmpos : 1 ≤ m := by omega
        obtain ⟨k, hsim, _⟩ := primedAll_sim w h m hmpos
        have hcut := hsim.forget.toCut
        obtain ⟨x, y, z, hxyz, hset⟩ := hcut.triangle_incidence _ _ _ ht'
        exact ⟨primedStageTime w h m, (x, y, z), hxyz, hset⟩
    obtain ⟨n, t', htglobal, hset⟩ := htri
    refine ⟨n, t', htglobal, ?_⟩
    have htriEq := (kmswMissingRootStage_agree u m).2.2.2.2.2.1
    have htOrd : t.1 ∈ (kmswStage u m).triangles := by
      rw [← htriEq]
      exact ht'
    obtain ⟨ha, hb, hc⟩ := triBound_stage u m t.1 htOrd
    have hNext := (kmswMissingRootStage_agree u m).2.1
    have ha' : t.1.1 < sh.nextEdge := by rw [hNext]; exact ha
    have hb' : t.1.2.1 < sh.nextEdge := by rw [hNext]; exact hb
    have hc' : t.1.2.2 < sh.nextEdge := by rw [hNext]; exact hc
    have hmapa := (primedLimit_maps_eq_of_allocated w h m).1 t.1.1 ha'
    have hmapb := (primedLimit_maps_eq_of_allocated w h m).1 t.1.2.1 hb'
    have hmapc := (primedLimit_maps_eq_of_allocated w h m).1 t.1.2.2 hc'
    simpa only [hmapa, hmapb, hmapc] using hset.symm
  · intro m hm
    exact ⟨primedDartMapOriented_inducedEmbedding w h m hm,
      primedDartMapOriented_inducedEmbedding_dartMap w h m hm⟩

end DirectedDistances.KMSW
