module

public import DirectedDistances.KMSW.HatFaceIso
public import DirectedDistances.KMSW.MhatPrimeFaceSource
public import DirectedDistances.KMSW.KMSWFutureMapCarrier
public import DirectedDistances.KMSW.HatMissingEdgeExclusion

/-! Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.

The coherent edge map transfers finite incidence from the ambient map. Missing-edge
exclusion gives its exact geometric image. The resulting dart equivalence preserves
root, edge reversal, missing tags and tail tags. Rotation is a separate obligation. -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Finite incidence, including geometric edges which are missing. -/
@[expose] def hatLimitFiniteIncidence (c : ℕ → Fin 3) : Prop :=
  ∀ v, {e : ℕ | ∃ n, e < (kmswStage c n).nextEdge ∧
    ((kmswStage c n).west e = v ∨ (kmswStage c n).east e = v)}.Finite

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every natural edge ID of the compressed walk is eventually present. -/
theorem hatCodes_edge_present (w : ℕ → Fin 3) (h : HasFlowLineHits w) (e : ℕ) :
    EdgePresent (hatCodes w h) e :=
  hatLocal_allocated_edge_present w h e e (kmsw_edge_allocated_by_self _ e)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The coherent edge-ID map is injective on all geometric edge IDs. -/
theorem hatLimitEdgeMap_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (hatLimitEdgeMap w h) := by
  intro e f hef
  exact hatLimit_edge_injOn (hatLimitExplicitInput w h)
    (hatCodes_edge_present w h e) (hatCodes_edge_present w h f) hef

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The exact image retains presence and both reachable endpoints. -/
theorem hatLimitEdgeMap_range_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w) (e : ℕ) :
    (∃ a, hatLimitEdgeMap w h a = e) ↔
      EdgePresent w e ∧ MhatGeometricEdge w e := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨hp, hw, he, -, -⟩ :=
      edge_data (hatLimitExplicitInput w h) (hatCodes_edge_present w h a)
    exact ⟨hp, hw, he⟩
  · rintro ⟨hp, hw, he⟩
    obtain ⟨a, -, hae⟩ := edge_cover (hatLimitExplicitInput w h) hp hw he
    exact ⟨a, hae⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The root edge ID is fixed by the coherent limit map. -/
theorem hatLimitEdgeMap_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    hatLimitEdgeMap w h 0 = 0 := by
  have hb : 0 < (kmswStage (hatCodes w h) 0).nextEdge := by
    change 0 < 1
    decide
  rw [hatLimitEdgeMap_eq_stage w h 0 0 hb]
  rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Compressed finite incidence follows from ambient finite incidence by edge-ID injection. -/
theorem hatCodes_finiteIncidence (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) : hatLimitFiniteIncidence (hatCodes w h) := by
  intro v
  apply Set.Finite.of_injOn (f := hatLimitEdgeMap w h)
    (t := {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = hatLimitVertexMap w h v ∨
        (kmswStage w n).east e = hatLimitVertexMap w h v)})
  · rintro e ⟨n, hn, hend⟩
    have hs := (hatLimitExplicitInput w h).stage_sim n
    refine ⟨quadrantRStageTime w h n, hs.edge_bound e hn, ?_⟩
    obtain ⟨hw, he⟩ := hs.incidence e hn
    rcases hend with hv | hv
    · exact Or.inl (hw.trans (congrArg (hatLimitVertexMap w h) hv))
    · exact Or.inr (he.trans (congrArg (hatLimitVertexMap w h) hv))
  · exact (hatLimitEdgeMap_injective w h).injOn
  · exact hfin (hatLimitVertexMap w h v)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The explicit edge bijection onto present geometric M-hat edges; no missing-edge -/
@[expose] noncomputable def hatPresentGeometricEdgeEquiv
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ℕ ≃ {e : ℕ // EdgePresent w e ∧ MhatGeometricEdge w e} :=
  Equiv.ofBijective
    (fun e => ⟨hatLimitEdgeMap w h e, (hatLimitEdgeMap_range_iff w h _).mp ⟨e, rfl⟩⟩)
    ⟨fun _ _ he => hatLimitEdgeMap_injective w h (congrArg Subtype.val he), by
      rintro ⟨e, he⟩
      obtain ⟨a, ha⟩ := (hatLimitEdgeMap_range_iff w h e).mpr he
      exact ⟨a, Subtype.ext ha⟩⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The coherent map of geometric darts retains the side bit and individual edge ID. -/
@[expose] noncomputable def hatLimitDartMap (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (d : ℕ × Bool) :
    {d : ℕ × Bool // MhatGeometricEdge w d.1} :=
  ⟨(hatLimitEdgeMap w h d.1, d.2),
    ((hatLimitEdgeMap_range_iff w h _).mp ⟨d.1, rfl⟩).2⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The geometric dart map is injective, including for parallel edges. -/
theorem hatLimitDartMap_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (hatLimitDartMap w h) := by
  intro d e hde
  apply Prod.ext
  · exact hatLimitEdgeMap_injective w h (congrArg (fun a => a.val.1) hde)
  · exact congrArg (fun a => a.val.2) hde

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result. -/
theorem hatLimitDartMap_root (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (hatLimitDartMap w h futureMapRootDart).val = futureMapRootDart := by
  change (hatLimitEdgeMap w h 0, false) = (0, false)
  rw [hatLimitEdgeMap_zero w h]

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Edge reversal intertwines without a rotation claim. -/
theorem hatLimitDartMap_edgeInv (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : ℕ × Bool) :
    (hatLimitDartMap w h (futureMapEdgeInv d)).val =
      futureMapEdgeInv (hatLimitDartMap w h d).val := rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Both dart missing tags agree; both edge IDs are eventually present. -/
theorem hatLimitDartMap_missing (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : ℕ × Bool) :
    futureMapMissing (hatCodes w h) d ↔
      futureMapMissing w (hatLimitDartMap w h d).val := by
  have hp := hatCodes_edge_present w h d.1
  have hq := ((hatLimitEdgeMap_range_iff w h _).mp ⟨d.1, rfl⟩).1
  exact ⟨fun hm => (hm hp).elim, fun hm => (hm hq).elim⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The side bit and eventual presence give identical tail tags. -/
theorem hatLimitDartMap_tail (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : ℕ × Bool) :
    futureMapTail (hatCodes w h) d ↔
      futureMapTail w (hatLimitDartMap w h d).val := by
  have hp := hatCodes_edge_present w h d.1
  have hq := ((hatLimitEdgeMap_range_iff w h _).mp ⟨d.1, rfl⟩).1
  exact ⟨fun ht => ⟨ht.1, hq⟩, fun ht => ⟨ht.1, hp⟩⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
For a geometric target dart, the exact remaining coverage condition is presence. -/
theorem hatLimitDartMap_range_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : {d : ℕ × Bool // MhatGeometricEdge w d.1}) :
    (∃ a, hatLimitDartMap w h a = d) ↔ EdgePresent w d.val.1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ((hatLimitEdgeMap_range_iff w h _).mp ⟨a.1, rfl⟩).1
  · intro hp
    obtain ⟨a, ha⟩ := (hatLimitEdgeMap_range_iff w h d.val.1).mpr ⟨hp, d.property⟩
    refine ⟨(a, d.val.2), Subtype.ext ?_⟩
    exact Prod.ext ha rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The flow-hit source domain already supplies the boundary-hit witnesses needed -/
theorem hatBoundaryHitWitnesses (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    BoundaryHitWitnesses w := by
  have hlevels : ∀ k : ℕ,
      (∃ n, L w n = -(k : ℤ)) ∧ (∃ n, R w n = -(k : ℤ)) := by
    intro k
    induction k with
    | zero => exact ⟨⟨0, by simp [L]⟩, ⟨0, by simp [R]⟩⟩
    | succ k ih =>
      obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := ih
      obtain ⟨n', -, hn'⟩ := h.1 n
      obtain ⟨m', -, hm'⟩ := h.2 m
      exact ⟨⟨n', by rw [hn', hn]; omega⟩, ⟨m', by rw [hm', hm]; omega⟩⟩
  constructor
  · intro k hk
    obtain ⟨n, hn⟩ := (hlevels k.toNat).2
    exact ⟨n, by omega⟩
  · intro k hk
    obtain ⟨n, hn⟩ := (hlevels (-k).toNat).1
    exact ⟨n, by omega⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The edge map covers every geometric M-hat edge, using proved missing-edge exclusion. -/
theorem hatLimitEdgeMap_geometric_range_iff (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (e : ℕ) :
    (∃ a, hatLimitEdgeMap w h a = e) ↔ MhatGeometricEdge w e := by
  constructor
  · intro he
    exact ((hatLimitEdgeMap_range_iff w h e).mp he).2
  · intro he
    exact (hatLimitEdgeMap_range_iff w h e).mpr
      ⟨mhatGeometricEdge_edgePresent w (hatBoundaryHitWitnesses w h) e he, he⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
An edge-ID bijection onto all geometric M-hat edges, retaining parallel edges. -/
@[expose] noncomputable def hatGeometricEdgeEquiv
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ℕ ≃ {e : ℕ // MhatGeometricEdge w e} :=
  Equiv.ofBijective
    (fun e => ⟨hatLimitEdgeMap w h e,
      (hatLimitEdgeMap_geometric_range_iff w h _).mp ⟨e, rfl⟩⟩)
    ⟨fun _ _ he => hatLimitEdgeMap_injective w h (congrArg Subtype.val he), by
      rintro ⟨e, he⟩
      obtain ⟨a, ha⟩ := (hatLimitEdgeMap_geometric_range_iff w h e).mpr he
      exact ⟨a, Subtype.ext ha⟩⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The geometric edge equivalence evaluates by the coherent edge map. -/
theorem hatGeometricEdgeEquiv_apply (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (e : ℕ) : (hatGeometricEdgeEquiv w h e).val = hatLimitEdgeMap w h e := rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every geometric target dart is covered, with missing-edge exclusion proved separately. -/
theorem hatLimitDartMap_surjective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Surjective (hatLimitDartMap w h) := by
  intro d
  exact (hatLimitDartMap_range_iff w h d).mpr
    (mhatGeometricEdge_edgePresent w (hatBoundaryHitWitnesses w h) d.val.1 d.property)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The dart equivalence onto geometric M-hat darts uses the coherent edge-ID map. -/
@[expose] noncomputable def hatLimitDartEquiv (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    (ℕ × Bool) ≃ {d : ℕ × Bool // MhatGeometricEdge w d.1} :=
  Equiv.ofBijective (hatLimitDartMap w h)
    ⟨hatLimitDartMap_injective w h, hatLimitDartMap_surjective w h⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The dart equivalence retains the side bit and evaluates by the coherent edge map. -/
theorem hatLimitDartEquiv_apply (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : ℕ × Bool) :
    (hatLimitDartEquiv w h d).val = (hatLimitEdgeMap w h d.1, d.2) := rfl

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Finite incidence and the root, edge-reversal, missing and tail clauses for the
unprimed dart equivalence. Rotation is not asserted. -/
theorem hatLimitDartIdentification (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) :
    ∃ _ : hatLimitFiniteIncidence (hatCodes w h),
      ∃ H : (ℕ × Bool) ≃ {d : ℕ × Bool // MhatGeometricEdge w d.1},
        (H futureMapRootDart).val = futureMapRootDart ∧
        (∀ d, (H (futureMapEdgeInv d)).val = futureMapEdgeInv (H d).val) ∧
        (∀ d, futureMapMissing (hatCodes w h) d ↔ futureMapMissing w (H d).val) ∧
        (∀ d, futureMapTail (hatCodes w h) d ↔ futureMapTail w (H d).val) := by
  exact ⟨hatCodes_finiteIncidence w h hfin, hatLimitDartEquiv w h,
    hatLimitDartMap_root w h, hatLimitDartMap_edgeInv w h,
    hatLimitDartMap_missing w h, hatLimitDartMap_tail w h⟩

end DirectedDistances.KMSW
