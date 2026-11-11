module

public import DirectedDistances.KMSW.PrimedComplementEdgeEquiv
public import DirectedDistances.KMSW.PrimedDartMapOriented
public import DirectedDistances.KMSW.MhatPrimeDrawing
public import DirectedDistances.KMSW.KMSWFutureMapCarrier
public import DirectedDistances.KMSW.PrimedGeometricEdgeCoverage
import DirectedDistances.KMSW.PrimedReachabilityUnion
import DirectedDistances.KMSW.HatMissingEdgeExclusion

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Finite incidence includes missing geometric edges. -/
@[expose] def primedLimitFiniteIncidence (u : ℕ → Fin 3) : Prop :=
  ∀ v, {e : ℕ | ∃ n, e < (kmswStage u n).nextEdge ∧
    ((kmswStage u n).west e = v ∨ (kmswStage u n).east e = v)}.Finite

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every edge ID, including every missing edge, has a distinct ambient image. -/
theorem primedLimitEdgeMap_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (primedLimitEdgeMap w h) := by
  intro e f hef
  exact (primedLimit_maps_injective_on_allocated w h).1
    ((primedLocalIds_eventually_allocated w h).1 e)
    ((primedLocalIds_eventually_allocated w h).1 f) hef

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The initial missing root retains its geometric edge ID under C18. -/
theorem primedLimitEdgeMap_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    primedLimitEdgeMap w h 0 = kmswLLCreatedEdge w (walkNL w h 0) := by
  rw [(primedLimit_maps_eq_of_allocated w h 0).1 0 (by change 0 < 1; decide)]
  exact primedInitialEdgeMap_root w _

private theorem limit_stage_incidence (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m e : ℕ) (he : e < (kmswStage (primedCode (primedSimInput w) h) m).nextEdge) :
    ∃ n, primedLimitEdgeMap w h e < (kmswStage w n).nextEdge ∧
      (((kmswStage w n).west (primedLimitEdgeMap w h e) =
          primedLimitVertexMap w h
            ((kmswStage (primedCode (primedSimInput w) h) m).west e) ∧
        (kmswStage w n).east (primedLimitEdgeMap w h e) =
          primedLimitVertexMap w h
            ((kmswStage (primedCode (primedSimInput w) h) m).east e)) ∨
       ((kmswStage w n).west (primedLimitEdgeMap w h e) =
          primedLimitVertexMap w h
            ((kmswStage (primedCode (primedSimInput w) h) m).east e) ∧
        (kmswStage w n).east (primedLimitEdgeMap w h e) =
          primedLimitVertexMap w h
            ((kmswStage (primedCode (primedSimInput w) h) m).west e))) := by
  let u := primedCode (primedSimInput w) h
  have ha := kmswMissingRootStage_agree u m
  have hel : e < (kmswMissingRootStage u m).nextEdge := by rwa [ha.2.1]
  have hev := kmswStage_endpoints_lt_nextVertex u m e he
  have hwv : (kmswMissingRootStage u m).west e <
      (kmswMissingRootStage u m).nextVertex := by
    rw [ha.2.2.1, ha.1]
    exact hev.1
  have hev' : (kmswMissingRootStage u m).east e <
      (kmswMissingRootStage u m).nextVertex := by
    rw [ha.2.2.2.1, ha.1]
    exact hev.2
  have hmap := (primedLimit_maps_eq_of_allocated w h m).1 e hel
  have hwest := (primedLimit_maps_eq_of_allocated w h m).2 _ hwv
  have heast := (primedLimit_maps_eq_of_allocated w h m).2 _ hev'
  have hbound : primedAllEdgeMap w h m e <
      (kmswStage w (primedStageTime w h m)).nextEdge := by
    cases m with
    | zero => exact (primedAll_sim_zero w h).1.edge_bound e hel
    | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact hs.edge_bound e hel
  refine ⟨primedStageTime w h m, by rwa [hmap], ?_⟩
  have hi := primedAll_endpoint_orders w h m ⟨e, hel⟩
  dsimp only at hi
  rw [← hwest, ← heast, ha.2.2.1, ha.2.2.2.1] at hi
  rwa [hmap]

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Ambient finite incidence transfers to the primed code without a coverage premise. -/
theorem primedCode_finiteIncidence (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) :
    primedLimitFiniteIncidence (primedCode (primedSimInput w) h) := by
  intro v
  apply Set.Finite.of_injOn (f := primedLimitEdgeMap w h)
    (t := {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = primedLimitVertexMap w h v ∨
        (kmswStage w n).east e = primedLimitVertexMap w h v)})
  · rintro e ⟨m, he, hv⟩
    obtain ⟨n, hn, hi⟩ := limit_stage_incidence w h m e he
    refine ⟨n, hn, ?_⟩
    rcases hi with ⟨hw, he⟩ | ⟨hw, he⟩ <;> rcases hv with hv | hv
    · exact Or.inl (hw.trans (congrArg (primedLimitVertexMap w h) hv))
    · exact Or.inr (he.trans (congrArg (primedLimitVertexMap w h) hv))
    · exact Or.inr (he.trans (congrArg (primedLimitVertexMap w h) hv))
    · exact Or.inl (hw.trans (congrArg (primedLimitVertexMap w h) hv))
  · exact (primedLimitEdgeMap_injective w h).injOn
  · exact hfin _

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
All limit edges preserve their unordered endpoints, including missing beta edges. -/
theorem primedLimitEdgeMap_endpoint_orders (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : ℕ) :
    let u := primedCode (primedSimInput w) h
    let E := primedLimitEdgeMap w h e
    let a := primedLimitVertexMap w h (edgeWest u e)
    let b := primedLimitVertexMap w h (edgeEast u e)
    (edgeWest w E = a ∧ edgeEast w E = b) ∨
      (edgeWest w E = b ∧ edgeEast w E = a) := by
  obtain ⟨n, hn, hi⟩ := limit_stage_incidence w h e e (kmsw_edge_allocated_by_self _ e)
  dsimp only
  rw [(edge_endpoints_eq w hn).1, (edge_endpoints_eq w hn).2,
    (edge_endpoints_eq _ (kmsw_edge_allocated_by_self _ e)).1,
    (edge_endpoints_eq _ (kmsw_edge_allocated_by_self _ e)).2] at hi
  exact hi

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The limit edge map identifies precisely the directed primed edges. -/
theorem primedLimitEdgeMap_present_iff (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : ℕ) :
    PrimedEdgePresent w h e ↔ primePresentEdge w (primedLimitEdgeMap w h e) := by
  constructor
  · intro he
    have hd := primedLimitEdge_data w h he
    refine ⟨hd.1, ?_⟩
    intro hg
    obtain ⟨n, hn⟩ := (stageReachablePresentEdges_iUnion_iff w _).mpr
      ⟨hd.1, hg.1, hg.2⟩
    exact hd.2.1 n hn
  · intro he
    have hnever : ∀ n, primedLimitEdgeMap w h e ∉ stageReachablePresentEdges w n := by
      intro n hn
      obtain ⟨_, hw, he'⟩ := (stageReachablePresentEdges_iUnion_iff w _).mp ⟨n, hn⟩
      exact he.2 ⟨hw, he'⟩
    obtain ⟨a, ha, hae⟩ := primedLimitEdgeComplement w h _ he.1 hnever
    have hae' := primedLimitEdgeMap_injective w h hae
    exact hae' ▸ ha

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The stable endpoint correction uses the ordered geometric endpoints. -/
@[expose] noncomputable def primedLimitSideFlip (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : ℕ) : Bool :=
  decide (primedLimitVertexMap w h
    (edgeWest (primedCode (primedSimInput w) h) e) ≠
      edgeWest w (primedLimitEdgeMap w h e))

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Present edges need no endpoint correction. -/
theorem primedLimitSideFlip_of_present (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) {e : ℕ} (he : PrimedEdgePresent w h e) :
    primedLimitSideFlip w h e = false := by
  have hw := (primedLimitEdge_data w h he).2.2.1
  simp only [primedLimitSideFlip, hw, ne_eq, not_true_eq_false, decide_false]

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The C18 root retains its endpoint order. -/
theorem primedLimitSideFlip_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    primedLimitSideFlip w h 0 = false := by
  have hv := (primedLimit_maps_eq_of_allocated w h 0).2 0 (by change 0 < 2; decide)
  have hb := (primedAll_sim_zero w h).1.edge_bound 0 (by change 0 < 1; decide)
  have hw : primedLimitVertexMap w h
      (edgeWest (primedCode (primedSimInput w) h) 0) =
        edgeWest w (primedLimitEdgeMap w h 0) := by
    change primedLimitVertexMap w h 0 = _
    rw [hv, primedLimitEdgeMap_zero]
    exact (edge_endpoints_eq w hb).1
  simp only [primedLimitSideFlip, hw, ne_eq, not_true_eq_false, decide_false]

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The geometric dart map corrects the endpoint order without discarding missing edges.
Its codomain is ambient darts until geometric coverage is proved. -/
@[expose] noncomputable def primedLimitDartMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (d : ℕ × Bool) : ℕ × Bool :=
  (primedLimitEdgeMap w h d.1, d.2 ^^ primedLimitSideFlip w h d.1)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The geometric dart map is injective on all darts. -/
theorem primedLimitDartMap_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (primedLimitDartMap w h) := by
  intro d e hde
  have he := primedLimitEdgeMap_injective w h (congrArg Prod.fst hde)
  have hs := congrArg Prod.snd hde
  change (d.2 ^^ primedLimitSideFlip w h d.1) =
    (e.2 ^^ primedLimitSideFlip w h e.1) at hs
  rw [he] at hs
  exact Prod.ext he (Bool.xor_left_inj.mp hs)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The initial root dart keeps its geometric image and side under C18. -/
theorem primedLimitDartMap_root (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    primedLimitDartMap w h futureMapRootDart =
      (kmswLLCreatedEdge w (walkNL w h 0), false) := by
  change (primedLimitEdgeMap w h 0, false ^^ primedLimitSideFlip w h 0) = _
  rw [primedLimitEdgeMap_zero, primedLimitSideFlip_zero]
  rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Geometric edge reversal commutes with the dart map for every missing or present edge. -/
theorem primedLimitDartMap_edgeInv (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : ℕ × Bool) :
    primedLimitDartMap w h (futureMapEdgeInv d) =
      futureMapEdgeInv (primedLimitDartMap w h d) := by
  apply Prod.ext
  · rfl
  · exact Bool.not_xor _ _

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Directed tail tags agree under the corrected dart map. -/
theorem primedLimitDartMap_tail (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : ℕ × Bool) :
    (d.2 = false ∧ PrimedEdgePresent w h d.1) ↔
      ((primedLimitDartMap w h d).2 = false ∧
        primePresentEdge w (primedLimitDartMap w h d).1) := by
  constructor
  · rintro ⟨hs, hp⟩
    refine ⟨?_, (primedLimitEdgeMap_present_iff w h d.1).mp hp⟩
    change (d.2 ^^ primedLimitSideFlip w h d.1) = false
    rw [hs, primedLimitSideFlip_of_present w h hp]
    rfl
  · rintro ⟨hs, hp⟩
    have hp' := (primedLimitEdgeMap_present_iff w h d.1).mpr hp
    refine ⟨?_, hp'⟩
    change (d.2 ^^ primedLimitSideFlip w h d.1) = false at hs
    rwa [primedLimitSideFlip_of_present w h hp', Bool.xor_false] at hs

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The limit correction agrees with every allocated finite-stage correction. -/
theorem primedLimitSideFlip_eq_stage (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    primedLimitSideFlip w h e.val = primedSideFlip w h m e := by
  let u := primedCode (primedSimInput w) h
  have ha := kmswMissingRootStage_agree u m
  have heb : e.val < (kmswStage u m).nextEdge := by
    rw [← ha.2.1]
    exact e.isLt
  have hwb : (kmswMissingRootStage u m).west e.val <
      (kmswMissingRootStage u m).nextVertex := by
    rw [ha.2.2.1, ha.1]
    exact (kmswStage_endpoints_lt_nextVertex u m e.val heb).1
  have hgb : primedAllEdgeMap w h m e.val <
      (kmswStage w (primedStageTime w h m)).nextEdge := by
    cases m with
    | zero => exact (primedAll_sim_zero w h).1.edge_bound _ e.isLt
    | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact hs.edge_bound _ e.isLt
  have hlocal : edgeWest u e.val = (kmswMissingRootStage u m).west e.val := by
    rw [ha.2.2.1]
    exact (edge_endpoints_eq u heb).1.symm
  have hvertex : primedLimitVertexMap w h (edgeWest u e.val) =
      primedAllVertexMap w h m ((kmswMissingRootStage u m).west e.val) := by
    rw [hlocal]
    exact (primedLimit_maps_eq_of_allocated w h m).2 _ hwb
  have hedge : edgeWest w (primedLimitEdgeMap w h e.val) =
      (kmswStage w (primedStageTime w h m)).west (primedAllEdgeMap w h m e.val) := by
    rw [(primedLimit_maps_eq_of_allocated w h m).1 _ e.isLt]
    exact (edge_endpoints_eq w hgb).1.symm
  change decide (primedLimitVertexMap w h (edgeWest u e.val) ≠ _) = _
  simp only [primedSideFlip, hvertex, hedge]
  rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The limit dart map restricts to the existing corrected finite-stage maps. -/
theorem primedLimitDartMap_eq_stage (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    primedLimitDartMap w h (d.1.val, d.2) =
      ((primedDartMapOriented w h m d).1.val, (primedDartMapOriented w h m d).2) := by
  apply Prod.ext
  · exact (primedLimit_maps_eq_of_allocated w h m).1 _ d.1.isLt
  · change (d.2 ^^ primedLimitSideFlip w h d.1.val) =
      (d.2 ^^ primedSideFlip w h m d.1)
    rw [primedLimitSideFlip_eq_stage]

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The C18 root is absent from the ambient directed edge set, while retaining geometry. -/
theorem primedLimitRoot_not_ambientPresent (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ¬ EdgePresent w (primedLimitEdgeMap w h 0) := by
  intro hp
  obtain ⟨N, hN⟩ := hp.eventually_present
  have hLL := (primedAll_sim_zero w h).1.missing_root.2.2
  have hmap := (primedLimit_maps_eq_of_allocated w h 0).1 0
    (by change 0 < 1; decide)
  rw [← hmap] at hLL
  have hf := (primedCrossing_LL_persistent w
    (Nat.le_max_right N (primedStageTime w h 0)) hLL).2.1
  have ht := (hN _ (Nat.le_max_left N (primedStageTime w h 0))).2
  rw [hf] at ht
  cases ht

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The C18 root is a retained missing edge of the primed geometric carrier. -/
theorem primedLimitRoot_primeMissingEdge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    primeMissingEdge w hfin hb (primedLimitEdgeMap w h 0) := by
  have hp := primedLimitRoot_not_ambientPresent w h
  refine ⟨Or.inl ?_, fun ht => hp ht.1⟩
  intro hg
  exact hp (mhatGeometricEdge_edgePresent w hb _ hg)



theorem primedLimitRoot_not_primedPresent (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : ¬ PrimedEdgePresent w h 0 := by
  rintro ⟨m, _, hp⟩
  rw [kmswMissingRootStage_present_zero] at hp
  cases hp

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The missing tag at any image edge is exactly nonpresence plus retained geometry.
No retained-geometry hypothesis is introduced to derive a target theorem. -/
theorem primedLimitEdgeMap_missing_iff (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ) :
    primeMissingEdge w hfin hb (primedLimitEdgeMap w h e) ↔
      primeGeomEdge w hfin hb (primedLimitEdgeMap w h e) ∧
        ¬ PrimedEdgePresent w h e := by
  constructor
  · rintro ⟨hg, hp⟩
    exact ⟨hg, fun he => hp ((primedLimitEdgeMap_present_iff w h e).mp he)⟩
  · rintro ⟨hg, hp⟩
    exact ⟨hg, fun he => hp ((primedLimitEdgeMap_present_iff w h e).mpr he)⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every image edge on beta zero has the missing primed tag. -/
theorem primedLimitEdgeMap_beta_missing (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ)
    (he : primeBetaEdge w hfin hb (primedLimitEdgeMap w h e)) :
    ¬ PrimedEdgePresent w h e := by
  exact ((primedLimitEdgeMap_missing_iff w h hfin hb e).mp
    (primeBetaEdge_primeMissingEdge w hfin hb _ he)).2

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The smallest remaining forward geometric-image obligation excludes the proved
C18 root and all proved present edges. This goal is not assumed. -/
@[expose] def primedMissingNonrootImageGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) : Prop :=
  ∀ e, e ≠ 0 → ¬ PrimedEdgePresent w h e →
    primeGeomEdge w hfin hb (primedLimitEdgeMap w h e)

end DirectedDistances.KMSW
