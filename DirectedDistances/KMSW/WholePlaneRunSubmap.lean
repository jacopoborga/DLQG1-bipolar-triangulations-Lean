module

public import DirectedDistances.KMSW.WholePlaneRightBoundaryChain

/-! Helper toward F4c / Lemma 3.10 (Remark 3.4,
whole-plane colimit; not the paper result. The arbitrary-vertex rotation-restriction target is
not established here; it is proved separately as `wholePlaneRotation_symm_firstReturn_run` in
`WholePlaneRunRotationRestrict.lean`. -/

public section
namespace DirectedDistances.KMSW

/-- Every colimit edge has a run representative; helper toward F4c / Lemma 3.10
submap of the whole-plane colimit; not the paper result. -/
theorem wholePlaneEdge_has_run_rep (W : ℤ → Fin 3) (e : WholePlaneEdge W) :
    ∃ N f, wholePlaneEdgeι W N f = e := by
  obtain ⟨⟨N, f⟩, h⟩ := Quotient.exists_rep e
  exact ⟨N, f, h⟩

/-- Every colimit vertex has a run representative; helper toward F4c / Lemma 3.10
submap of the whole-plane colimit; not the paper result. -/
theorem wholePlaneVertex_has_run_rep (W : ℤ → Fin 3) (v : WholePlaneVertex W) :
    ∃ N x, wholePlaneVertexι W N x = v := by
  obtain ⟨⟨N, x⟩, h⟩ := Quotient.exists_rep v
  exact ⟨N, x, h⟩

/-- Every colimit dart has a run representative; helper toward F4c / Lemma 3.10
submap of the whole-plane colimit; not the paper result. -/
theorem wholePlaneDart_has_run_rep (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    ∃ N x, wholePlaneDartι W N x = d := by
  obtain ⟨⟨N, e⟩, he⟩ := Quotient.exists_rep d.1
  exact ⟨N, (e, d.2), Prod.ext he rfl⟩

private theorem runPresent_trans (W : ℤ → Fin 3) (N M : ℕ) (hNM : N ≤ M)
    (e : ℕ) (hp : EdgePresent (shiftedStream W N) e) :
    EdgePresent (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e) := by
  obtain ⟨n, he, hp⟩ := hp
  let s := M - N
  have he' : e < (kmswStage (fun i => shiftedStream W M (s + i)) n).nextEdge := by
    simpa only [s, shiftedStream_shift W N M hNM] using he
  have hp' : (kmswStage (fun i => shiftedStream W M (s + i)) n).present e = true := by
    simpa only [s, shiftedStream_shift W N M hNM] using hp
  have hrel := kmswWindowPatchData_rel (shiftedStream W M) s n
  have hb := hrel.edge_bound e he'
  have ht := hrel.present e he' hp'
  have hmap := kmswWindowEdgeMapInf_eq_stage (shiftedStream W M) s n e he'
  refine ⟨s + n, ?_, ?_⟩
  · change kmswWindowEdgeMapInf (shiftedStream W M) s e < _
    rw [hmap]
    exact hb
  · change (kmswStage (shiftedStream W M) (s + n)).present
      (kmswWindowEdgeMapInf (shiftedStream W M) s e) = true
    rw [hmap]
    exact ht

/-- Run-present edges remain present in each later run (`EdgePresent (shiftedStream W M) …`).
Colimit presence is `wholePlaneRun_present_colimit`. The converse need not hold: LL edges can
be missing in a run and become present in a later run. Helper toward F4c / Lemma 3.10 (Remark 3.4, -/
theorem wholePlaneRun_present_mono (W : ℤ → Fin 3) (N M : ℕ) (hNM : N ≤ M)
    (e : ℕ) (hp : EdgePresent (shiftedStream W N) e) :
    EdgePresent (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e) :=
  runPresent_trans W N M hNM e hp

/-- LL edges. Helper toward F4c / Lemma 3.10 (Remark 3.4, -/
theorem wholePlaneRun_present_colimit (W : ℤ → Fin 3) (N : ℕ) (e : ℕ)
    (hp : EdgePresent (shiftedStream W N) e) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N e) := by
  rw [wholePlaneEdgePresent_ι]
  exact ⟨N, le_rfl, fun M hNM => wholePlaneRun_present_mono W N M hNM e hp⟩

end DirectedDistances.KMSW
