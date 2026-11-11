module

public import DirectedDistances.KMSW.MonotoneSeamAffine
public import DirectedDistances.PlanarMap.PiecewiseLinearInterp
public import DirectedDistances.PlanarMap.PastTransferMap
public import DirectedDistances.PlanarMap.PLDrawingTransfer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace DirectedDistances.KMSW.PastDrawingTransfer

open DirectedDistances.PlanarMap Set

noncomputable section

variable (w0 wp : ℕ → Fin 3) (h0 : BoundaryHitWitnesses w0)
  (hp : BoundaryHitWitnesses wp)
  (hfin0 : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w0 n).nextEdge ∧
    ((kmswStage w0 n).west e = v ∨ (kmswStage w0 n).east e = v)}.Finite)
  (hfinp : ∀ v, {e : ℕ | ∃ n, e < (kmswStage wp n).nextEdge ∧
    ((kmswStage wp n).west e = v ∨ (kmswStage wp n).east e = v)}.Finite)




@[expose] def a (k : ℤ) : ℝ := seamX wp hp hfinp k








@[expose] def b (k : ℤ) : ℝ := -(seamX w0 h0 hfin0 (1 - k))




theorem a_strictMono : StrictMono (a wp hp hfinp) := seamX_strictMono wp hp hfinp




theorem b_strictMono : StrictMono (b w0 h0 hfin0) := by
  intro i j hij
  have hrev : (1 : ℤ) - j < 1 - i := by omega
  exact neg_lt_neg (seamX_strictMono w0 h0 hfin0 hrev)




theorem a_unbounded_above (M : ℝ) : ∃ k, M < a wp hp hfinp k :=
  (seamX_unbounded wp hp hfinp M).1




theorem a_unbounded_below (M : ℝ) : ∃ k, a wp hp hfinp k < M := by
  simpa only [a, neg_neg] using (seamX_unbounded wp hp hfinp (-M)).2




theorem b_unbounded_above (M : ℝ) : ∃ k, M < b w0 h0 hfin0 k := by
  obtain ⟨k, hk⟩ := (seamX_unbounded w0 h0 hfin0 M).2
  refine ⟨1 - k, ?_⟩
  dsimp [b]
  have hindex : (1 : ℤ) - (1 - k) = k := by omega
  rw [hindex]
  linarith only [hk]




theorem b_unbounded_below (M : ℝ) : ∃ k, b w0 h0 hfin0 k < M := by
  obtain ⟨k, hk⟩ := (seamX_unbounded w0 h0 hfin0 (-M)).1
  refine ⟨1 - k, ?_⟩
  dsimp [b]
  have hindex : (1 : ℤ) - (1 - k) = k := by omega
  rw [hindex]
  linarith only [hk]




@[expose] def phi : ℝ ≃o ℝ :=
  pwInterpOrderIso (a wp hp hfinp) (b w0 h0 hfin0)
    (a_strictMono wp hp hfinp) (b_strictMono w0 h0 hfin0)
    (a_unbounded_above wp hp hfinp) (a_unbounded_below wp hp hfinp)
    (b_unbounded_above w0 h0 hfin0) (b_unbounded_below w0 h0 hfin0)




theorem phi_breakpoint (k : ℤ) :
    phi w0 wp h0 hp hfin0 hfinp (a wp hp hfinp k) = b w0 h0 hfin0 k :=
  pwInterp_breakpoint (a_strictMono wp hp hfinp)
    (a_unbounded_above wp hp hfinp) (a_unbounded_below wp hp hfinp) k




theorem phi_strip (k : ℤ) :
    ∃ m c : ℝ, 0 < m ∧ ∀ x ∈ Icc (a wp hp hfinp k) (a wp hp hfinp (k + 1)),
      phi w0 wp h0 hp hfin0 hfinp x = m * x + c := by
  let m := (b w0 h0 hfin0 (k + 1) - b w0 h0 hfin0 k) /
    (a wp hp hfinp (k + 1) - a wp hp hfinp k)
  refine ⟨m, b w0 h0 hfin0 k - m * a wp hp hfinp k,
    pwAffine_slope_pos (a_strictMono wp hp hfinp) (b_strictMono w0 h0 hfin0) k, ?_⟩
  intro x hx
  rw [phi, pwInterpOrderIso_eq_of_mem_Icc _ _ _ _ _ _ hx]
  dsimp [m]
  ring




@[expose] def transfer : ℂ ≃ₜ ℂ :=
  pastTransferHomeomorph (phi w0 wp h0 hp hfin0 hfinp)
    (seamFun w0 h0 hfin0) (seamFun wp hp hfinp)
    (seamFun_continuous w0 h0 hfin0) (seamFun_continuous wp hp hfinp)




@[expose] def cuts : Set ℝ :=
  seamCutSet wp hp hfinp ∪ {x | -(phi w0 wp h0 hp hfin0 hfinp x) ∈
    seamCutSet w0 h0 hfin0}




theorem cuts_inter_Icc_finite (s t : ℝ) :
    (cuts w0 wp h0 hp hfin0 hfinp ∩ Icc s t).Finite := by
  let p := phi w0 wp h0 hp hfin0 hfinp
  have hi : Function.Injective (fun x : ℝ => -(p x)) := by
    intro x y hxy
    exact p.injective (neg_injective hxy)
  have hf := (seamCutSet_inter_Icc_finite w0 h0 hfin0 (-(p t)) (-(p s))).preimage
    (fun _ _ _ _ hxy => hi hxy)
  have hpfin : ({x | -(p x) ∈ seamCutSet w0 h0 hfin0} ∩ Icc s t).Finite := by
    apply hf.subset
    intro x hx
    exact ⟨hx.1, neg_le_neg (p.monotone hx.2.2), neg_le_neg (p.monotone hx.2.1)⟩
  have hu := (seamCutSet_inter_Icc_finite wp hp hfinp s t).union hpfin
  apply hu.subset
  intro x hx
  rcases hx.1 with hxp | hx0
  · exact Or.inl ⟨hxp, hx.2⟩
  · exact Or.inr ⟨hx0, hx.2⟩




theorem a_mem_cuts (k : ℤ) : a wp hp hfinp k ∈ cuts w0 wp h0 hp hfin0 hfinp := by
  exact Or.inl (mem_iUnion.mpr ⟨k, seamX_mem_seamCuts wp hp hfinp k⟩)




theorem interval_in_strip (s t : ℝ) (_hst : s < t)
    (hno : ∀ c ∈ cuts w0 wp h0 hp hfin0 hfinp, c ∉ Ioo s t) :
    ∃ k : ℤ, Icc s t ⊆ Icc (a wp hp hfinp k) (a wp hp hfinp (k + 1)) := by
  obtain ⟨k, hk, _⟩ := existsUnique_breakpointInterval (a_strictMono wp hp hfinp)
    (a_unbounded_above wp hp hfinp) (a_unbounded_below wp hp hfinp) s
  have ht : t ≤ a wp hp hfinp (k + 1) := by
    by_contra ht
    exact hno _ (a_mem_cuts w0 wp h0 hp hfin0 hfinp (k + 1))
      ⟨hk.2, lt_of_not_ge ht⟩
  exact ⟨k, fun _ hx => ⟨hk.1.trans hx.1, hx.2.trans ht⟩⟩




theorem transfer_affine (s t : ℝ) (hst : s < t)
    (hno : ∀ c ∈ cuts w0 wp h0 hp hfin0 hfinp, c ∉ Ioo s t) :
    ∃ m0 m1 c0 c1 : ℝ, 0 < m0 ∧ ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
      transfer w0 wp h0 hp hfin0 hfinp z =
        ⟨-(m0 * z.re) + c0, -z.im + m1 * z.re + c1⟩ := by
  obtain ⟨k, hk⟩ := interval_in_strip w0 wp h0 hp hfin0 hfinp s t hst hno
  obtain ⟨m, c, hm, hphi⟩ := phi_strip w0 wp h0 hp hfin0 hfinp k
  have hphi' : ∀ x ∈ Icc s t, phi w0 wp h0 hp hfin0 hfinp x = m * x + c :=
    fun x hx => hphi x (hk hx)
  obtain ⟨mp, cp, hfp⟩ := seamFun_affine_of_noCut wp hp hfinp s t hst
    (fun x hx => hno x (Or.inl hx))
  obtain ⟨m0, c0, hf0⟩ := seamFun_neg_orderIso_affine_of_noCut_preimage
    w0 h0 hfin0 (phi w0 wp h0 hp hfin0 hfinp) s t m c hm hphi'
    (fun x hx hcut => hno x (Or.inr hcut) hx)
  refine ⟨m, m0 + mp, -c, c0 + cp, hm, ?_⟩
  intro z hs ht
  change pastTransfer _ _ _ z = _
  apply Complex.ext
  · change -(phi w0 wp h0 hp hfin0 hfinp z.re) = _
    rw [hphi' z.re ⟨hs, ht⟩]
    ring
  · change -z.im + seamFun w0 h0 hfin0 (-(phi w0 wp h0 hp hfin0 hfinp z.re)) +
        seamFun wp hp hfinp z.re = _
    rw [hf0 z.re ⟨hs, ht⟩, hfp z.re ⟨hs, ht⟩]
    ring




theorem drawing_arc_monotone (d : ℕ × Bool) :
    ((monotoneFamilyDrawing wp hfinp (monotone_family_all wp)).arc d).XMonotone ∨
      ((monotoneFamilyDrawing wp hfinp (monotone_family_all wp)).arc d).reverse.XMonotone := by
  rcases d with ⟨e, b⟩
  have he := kmsw_edge_allocated_by_self wp e
  have hh : (monotoneFamilyDrawing wp hfinp (monotone_family_all wp)).arc (e, b) =
      if b then (layoutArc wp e e).reverse else layoutArc wp e e :=
    monotoneLimitDrawing_arc_layout wp hfinp _ e e he b
  rw [hh]
  cases b
  · exact Or.inl (layoutArc_points_pairwise wp e e he)
  · right
    change (layoutArc wp e e).reverse.reverse.XMonotone
    rw [Polyline.reverse_reverse]
    exact layoutArc_points_pairwise wp e e he




theorem pastDrawing_transfer :
    let Pp := monotoneFamilyDrawing wp hfinp (monotone_family_all wp)
    let T := transfer w0 wp h0 hp hfin0 hfinp
    ∃ P' : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
        (kmswInfRot wp hfinp) (kmswLimitDartVertex wp),
      P'.pos = T ∘ Pp.pos ∧ ∀ d,
        (P'.arc d).image = T '' (Pp.arc d).image ∧
        (P'.arc d).interior = T '' (Pp.arc d).interior := by
  exact PLDrawing.transfer (monotoneFamilyDrawing wp hfinp (monotone_family_all wp))
    (drawing_arc_monotone wp hfinp) (transfer w0 wp h0 hp hfin0 hfinp)
    (cuts w0 wp h0 hp hfin0 hfinp) (cuts_inter_Icc_finite w0 wp h0 hp hfin0 hfinp)
    (transfer_affine w0 wp h0 hp hfin0 hfinp)




theorem seam_vertex_position (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) (k : ℤ) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos (boundaryVertex w h k) =
      ⟨seamX w h hfin k, seamFun w h hfin (seamX w h hfin k)⟩ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let d := futureMapBoundaryDart w h k
  have hf : kmswLimitDartVertex w (futureMapEdgeInv d) = boundaryVertex w h k :=
    (futureMapBoundaryDart_endpoints w h k).2
  have he : (P.arc d).finish = P.pos (boundaryVertex w h k) := by
    calc
      (P.arc d).finish = P.pos (kmswLimitDartVertex w (futureMapEdgeInv d)) := by
        simpa [P, d, futureMapBoundaryDart, futureMapEdgeInv] using P.arc_finish d
      _ = P.pos (boundaryVertex w h k) := congrArg P.pos hf
  have himage : (P.arc d).finish ∈ (P.arc d).image := by
    rw [← Polyline.point_last_eq_finish]
    apply Polyline.point_mem_image
    have := List.length_pos_iff.mpr (P.arc d).nonempty
    omega
  have hg : (P.arc d).finish ∈ {z : ℂ | z.im = seamFun w h hfin z.re} := by
    rw [seamFun_graph]
    exact mem_iUnion.mpr ⟨k, himage⟩
  rw [he] at hg
  exact Complex.ext rfl hg




theorem transfer_seam_vertex (k : ℤ) :
    transfer w0 wp h0 hp hfin0 hfinp
        ((monotoneFamilyDrawing wp hfinp (monotone_family_all wp)).pos
          (boundaryVertex wp hp k)) =
      (monotoneFamilyDrawing w0 hfin0 (monotone_family_all w0)).pos
        (boundaryVertex w0 h0 (1 - k)) := by
  rw [seam_vertex_position wp hp hfinp k, seam_vertex_position w0 h0 hfin0 (1 - k)]
  have hphi : phi w0 wp h0 hp hfin0 hfinp (seamX wp hp hfinp k) =
      -(seamX w0 h0 hfin0 (1 - k)) := phi_breakpoint w0 wp h0 hp hfin0 hfinp k
  change pastTransfer _ _ _ _ = _
  apply Complex.ext
  · change -(phi w0 wp h0 hp hfin0 hfinp (seamX wp hp hfinp k)) = _
    rw [hphi, neg_neg]
  · change -seamFun wp hp hfinp (seamX wp hp hfinp k) +
        seamFun w0 h0 hfin0 (-(phi w0 wp h0 hp hfin0 hfinp (seamX wp hp hfinp k))) +
        seamFun wp hp hfinp (seamX wp hp hfinp k) = _
    rw [hphi, neg_neg]
    ring

end
end DirectedDistances.KMSW.PastDrawingTransfer
