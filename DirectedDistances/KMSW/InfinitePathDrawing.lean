module

public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.MonotoneLimitDrawing
public import DirectedDistances.PlanarMap.InfiniteRayStrip

/-! # Drawing infinite present paths

Helpers toward Lemma 4.6 (lem-geo-exist); not a paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem pathEdgeList_last_endpoint {w : ℕ → Fin 3}
    {u v : PresentVertex w} (p : Quiver.Path u v) {e : ℕ}
    (he : e ∈ (pathEdgeList p).getLast?) : edgeEast w e = v.id := by
  induction p with
  | nil => simp [pathEdgeList] at he
  | @cons b c q f ih =>
    have heq' : f.val = e := by simpa [pathEdgeList] using he
    have heq : e = f.val := heq'.symm
    subst e
    exact f.property.2.2

private theorem pathEdgeList_chain {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Quiver.Path u v) :
    List.IsChain (fun e f => edgeEast w e = edgeWest w f) (pathEdgeList p) := by
  induction p with
  | nil => exact List.isChain_nil
  | @cons b c q f ih =>
    rw [pathEdgeList]
    apply List.IsChain.append ih (List.isChain_singleton _)
    intro e he g hg
    have hg'' : f.val = g := by simpa using hg
    have hg' : g = f.val := hg''.symm
    subst g
    exact (pathEdgeList_last_endpoint q he).trans f.property.2.1.symm

/-- Consecutive edge IDs in an infinite present path meet east-to-west.
Uses only `edge`, `initial`, and `prefix_edges` from `InfinitePresentPath`
(`InfiniteGeodesic.lean:1011-1015`). Helper toward Lemma 4.6 (lem-geo-exist); -/
theorem infinitePresentPath_edge_chain {w : ℕ → Fin 3}
    {start : PresentVertex w} (Q : InfinitePresentPath w start) (i : ℕ) :
    edgeEast w (Q.edge i) = edgeWest w (Q.edge (i + 1)) := by
  let p := (Q.initial (i + 2)).2
  have hc := pathEdgeList_chain p
  rw [Q.prefix_edges (i + 2)] at hc
  rw [List.isChain_iff_getElem] at hc
  have hr := hc i (by rw [List.length_ofFn]; omega)
  simpa only [List.getElem_ofFn] using hr

private theorem forwardArc_eq_layoutArc (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ P : StageDrawing w n,
      Nonempty (MonotoneStageInvariant w n P)) (e : ℕ)
    (he : e < (kmswStage w e).nextEdge) :
    (monotoneLimitDrawing w hfin hfam).arc (e, false) = layoutArc w e e := by
  rw [monotoneLimitDrawing_arc_layout w hfin hfam e e he false]
  simp

/-- Every forward arc of an infinite present path is x-monotone in the
monotone limit drawing. Helpers toward Lemma 4.6 (lem-geo-exist); not a paper -/
theorem infinitePresentPath_arc_xMonotone {w : ℕ → Fin 3}
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ P : StageDrawing w n,
      Nonempty (MonotoneStageInvariant w n P))
    {start : PresentVertex w} (Q : InfinitePresentPath w start) (i : ℕ) :
    ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).XMonotone := by
  have he : Q.edge i < (kmswStage w (Q.edge i)).nextEdge :=
    kmsw_edge_allocated_by_self w (Q.edge i)
  rw [forwardArc_eq_layoutArc w hfin hfam _ he]
  exact layoutArc_points_pairwise w (Q.edge i) (Q.edge i) he

/-- Each forward path arc has strictly increasing endpoint abscissas.
Helpers toward Lemma 4.6 (lem-geo-exist); not a paper result. Source: -/
theorem infinitePresentPath_arc_start_re_lt_finish_re {w : ℕ → Fin 3}
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ P : StageDrawing w n,
      Nonempty (MonotoneStageInvariant w n P))
    {start : PresentVertex w} (Q : InfinitePresentPath w start) (i : ℕ) :
    ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.re <
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.re := by
  have he : Q.edge i < (kmswStage w (Q.edge i)).nextEdge :=
    kmsw_edge_allocated_by_self w (Q.edge i)
  rw [forwardArc_eq_layoutArc w hfin hfam _ he]
  obtain ⟨hs, hf⟩ := layoutArc_endpoints w (Q.edge i) (Q.edge i) he
  rw [hs, hf]
  change ((kmswStageRank w (Q.edge i)
    ((kmswStage w (Q.edge i)).west (Q.edge i)) : ℚ) : ℝ) <
    ((kmswStageRank w (Q.edge i)
      ((kmswStage w (Q.edge i)).east (Q.edge i)) : ℚ) : ℝ)
  exact_mod_cast kmswStageRank_strict w (Q.edge i) (Q.edge i) he

/-- Consecutive forward arcs meet at the position of their common path vertex.
The endpoint identity uses `edge` and the finite-prefix path certificates from
`InfinitePresentPath` (`InfiniteGeodesic.lean:1011-1015`). Helpers toward
Lemma 4.6 (lem-geo-exist); not a paper result. Source: -/
theorem infinitePresentPath_arc_seam {w : ℕ → Fin 3}
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ P : StageDrawing w n,
      Nonempty (MonotoneStageInvariant w n P))
    {start : PresentVertex w} (Q : InfinitePresentPath w start) (i : ℕ) :
    ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish =
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge (i + 1), false)).start := by
  let G := monotoneLimitDrawing w hfin hfam
  rw [G.arc_finish, G.arc_start]
  change G.pos (edgeEast w (Q.edge i)) = G.pos (edgeWest w (Q.edge (i + 1)))
  exact congrArg G.pos (infinitePresentPath_edge_chain Q i)

/-- The forward path's starting abscissas are strictly increasing.
Helpers toward Lemma 4.6 (lem-geo-exist); not a paper result. Source: -/
theorem infinitePresentPath_start_re_strictMono {w : ℕ → Fin 3}
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ P : StageDrawing w n,
      Nonempty (MonotoneStageInvariant w n P))
    {start : PresentVertex w} (Q : InfinitePresentPath w start) :
    StrictMono (fun i =>
      ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.re) := by
  apply strictMono_nat_of_lt_succ
  intro i
  calc
    ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).start.re <
        ((monotoneLimitDrawing w hfin hfam).arc (Q.edge i, false)).finish.re :=
      infinitePresentPath_arc_start_re_lt_finish_re hfin hfam Q i
    _ = ((monotoneLimitDrawing w hfin hfam).arc (Q.edge (i + 1), false)).start.re :=
      congrArg Complex.re (infinitePresentPath_arc_seam hfin hfam Q i)

end DirectedDistances.KMSW
