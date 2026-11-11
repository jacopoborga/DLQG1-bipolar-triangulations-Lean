module

public import DirectedDistances.KMSW.MonotoneLayoutInvariant
public import DirectedDistances.KMSW.MonotoneStageFaces
public import DirectedDistances.KMSW.LimitExternalFace
public import DirectedDistances.PlanarMap.GraphRegion
public import DirectedDistances.PlanarMap.GraphRegionClosure
public import DirectedDistances.PlanarMap.GraphRegionWedge
import DirectedDistances.PlanarMap.MonotonePolyline







public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology




@[expose] def monotoneLimitStageRegion (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (n : ℕ) : Set ℂ :=
  closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper




@[expose] def monotoneLimitExteriorRegion (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n)) : Set ℂ :=
  (⋃ n, monotoneLimitStageRegion w Q G n)ᶜ





@[expose] def MonotoneLimitCapPersistence (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n)) : Prop :=
  ∀ n (i : Fin (kmswStage w n).triangles.length) m, n ≤ m →
    ∃ j : Fin (kmswStage w m).triangles.length,
      ((G n).cap i).region = ((G m).cap j).region

private theorem stageTrace_subset_Pimage {w : ℕ → Fin 3} {n : ℕ}
    (Q : StageDrawing w n)
    {flip : ℕ × Bool → ℕ × Bool} {rot : Equiv.Perm (ℕ × Bool)}
    {vert : ℕ × Bool → ℕ}
    (P : PLDrawing (ℕ × Bool) ℕ flip rot vert)
    (harc : ∀ d : StageDart (kmswStage w n).nextEdge,
      P.arc (d.1.val, d.2) = Q.arc d) (e : ℕ) :
    stageEdgeTrace Q e ⊆ P.image := by
  intro z hz
  by_cases he : e < (kmswStage w n).nextEdge
  · simp only [stageEdgeTrace, dite_eq_left he] at hz
    change z ∈ Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image}
    exact Or.inr ⟨(e, false), by rw [harc ⟨⟨e, he⟩, false⟩]; exact hz⟩
  · simp [stageEdgeTrace, he] at hz

private theorem stageImage_subset_of_le {w : ℕ → Fin 3} (Q : ∀ n, StageDrawing w n)
    {rot : Equiv.Perm (ℕ × Bool)} {vert : ℕ × Bool → ℕ}
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) rot vert)
    (hpos : ∀ n v, P.pos v.val = (Q n).pos v)
    (harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d)
    {m k : ℕ} (hmk : m ≤ k) : (Q m).image ⊆ (Q k).image := by
  intro z hz
  change z ∈ Set.range (Q m).pos ∪ {z | ∃ d, z ∈ ((Q m).arc d).image} at hz
  rcases hz with ⟨v, hv⟩ | ⟨d, hd⟩
  · apply Or.inl
    let v' := v.castLE (CutConverse.nextVertex_mono w hmk)
    refine ⟨v', ?_⟩
    calc
      (Q k).pos v' = P.pos v'.val := (hpos k v').symm
      _ = P.pos v.val := by simp [v']
      _ = (Q m).pos v := hpos m v
      _ = z := hv
  · apply Or.inr
    let d' : StageDart (kmswStage w k).nextEdge :=
      (d.1.castLE (kmswStage_nextEdge_mono w hmk), d.2)
    refine ⟨d', ?_⟩
    have harcEq : (Q m).arc d = (Q k).arc d' := by
      calc
        (Q m).arc d = P.arc (d.1.val, d.2) := (harc m d).symm
        _ = (Q k).arc d' := harc k d'
    rw [← harcEq]
    exact hd

private theorem limitImage_subset_stageImages {w : ℕ → Fin 3}
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (Q : ∀ n, StageDrawing w n)
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (hpos : ∀ n v, P.pos v.val = (Q n).pos v)
    (harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d) :
    P.image ⊆ ⋃ n, (Q n).image := by
  intro z hz
  change z ∈ Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image} at hz
  rcases hz with ⟨v, hv⟩ | ⟨d, hd⟩
  · obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence w hfin v
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change z ∈ Set.range (Q n).pos ∪ {z | ∃ d, z ∈ ((Q n).arc d).image}
    apply Or.inl
    refine ⟨⟨v, hn⟩, ?_⟩
    calc
      (Q n).pos ⟨v, hn⟩ = P.pos v := (hpos n ⟨v, hn⟩).symm
      _ = z := hv
  · let n := d.1
    have he : d.1 < (kmswStage w n).nextEdge := by
      exact kmsw_edge_allocated_by_self w d.1
    let d' : StageDart (kmswStage w n).nextEdge := (⟨d.1, he⟩, d.2)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change z ∈ Set.range (Q n).pos ∪ {z | ∃ d, z ∈ ((Q n).arc d).image}
    apply Or.inr
    refine ⟨d', ?_⟩
    have hval : (d'.1.val, d'.2) = d := by simp [d']
    rw [← harc n d']
    rw [hval]
    exact hd

private theorem cap_avoids_limitImage {w : ℕ → Fin 3}
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (hpos : ∀ n v, P.pos v.val = (Q n).pos v)
    (harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d)
    (hpersist : MonotoneLimitCapPersistence w Q G) (n : ℕ)
    (i : Fin (kmswStage w n).triangles.length) :
    Disjoint ((G n).cap i).region P.image := by
  apply disjoint_left.mpr
  intro z hzCap hzImage
  obtain ⟨m, hzm⟩ := mem_iUnion.mp
    (limitImage_subset_stageImages hfin Q P hpos harc hzImage)
  let k := max n m
  obtain ⟨j, hcap⟩ := hpersist n i k (le_max_left _ _)
  have hzCapK : z ∈ ((G k).cap j).region := by
    rw [← hcap]
    exact hzCap
  have hzImageK : z ∈ (Q k).image :=
    stageImage_subset_of_le Q P hpos harc (le_max_right _ _) hzm
  exact (disjoint_left.mp ((G k).cap_avoid j)) hzCapK hzImageK

private theorem cap_frontier_subset_limitImage {w : ℕ → Fin 3}
    {n : ℕ} {Q : StageDrawing w n} (G : MonotoneStageInvariant w n Q)
    {flip : ℕ × Bool → ℕ × Bool} {rot : Equiv.Perm (ℕ × Bool)}
    {vert : ℕ × Bool → ℕ} (P : PLDrawing (ℕ × Bool) ℕ flip rot vert)
    (harc : ∀ d : StageDart (kmswStage w n).nextEdge,
      P.arc (d.1.val, d.2) = Q.arc d)
    (i : Fin (kmswStage w n).triangles.length) :
    frontier (G.cap i).region ⊆ P.image := by
  change frontier (graphRegion _ _ _ _) ⊆ P.image
  rw [frontier_graphRegion_eq (G.cap i).ab (G.cap i).low_continuous
    (G.cap i).high_continuous (G.cap i).separated
    (G.cap i).left_join (G.cap i).right_join]
  rw [G.cap_lower_trace i, G.cap_upper_trace i]
  rintro z (hz | hz)
  · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    exact stageTrace_subset_Pimage Q P harc e hz
  · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    exact stageTrace_subset_Pimage Q P harc e hz

private theorem cap_low_le_high {C : GraphCap} :
    ∀ x ∈ Icc C.a C.b, C.low x ≤ C.high x := by
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hax | hax
  · rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · exact (C.separated x ⟨hax, hxb⟩).le
    · rw [hxb, C.right_join]
  · rw [← hax, C.left_join]

private theorem cap_subset_stageRegion {w : ℕ → Fin 3} {n : ℕ}
    {Q : StageDrawing w n} (G : MonotoneStageInvariant w n Q)
    (i : Fin (kmswStage w n).triangles.length) :
    ((G.cap i).region) ⊆
      closedGraphRegion G.xmin G.xmax G.lower G.upper := by
  rw [← G.toMonotoneStageCertificate.cover]
  intro z hz
  exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hz⟩)

private theorem stageImage_subset_stageRegion {w : ℕ → Fin 3} {n : ℕ}
    {Q : StageDrawing w n} (G : MonotoneStageInvariant w n Q) :
    Q.image ⊆ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
  rw [← G.toMonotoneStageCertificate.cover]
  exact subset_union_left

/-- A fixed eastward upper-boundary wedge radius works for every closed graph region
whose upper graph agrees locally with the dart segment. Helper toward adjudication n308; -/
theorem wedge_compl_closedGraphRegion_east_upper_uniform (p dir : ℂ) (η : ℝ)
    (hd : 0 < dir.re) (hη : 0 < η) :
    ∃ δ > 0, ∀ (a b : ℝ) (f g : ℝ → ℝ),
      (∀ x ∈ Icc p.re (p.re + η),
        g x = p.im + (dir.im / dir.re) * (x - p.re)) →
      ∀ t ε, 0 < t → t < δ → 0 < ε → ε < δ →
        wedgePoint p dir t ε ∉ closedGraphRegion a b f g := by
  let s := dir.im / dir.re
  let fl : ℝ → ℝ := fun x => p.im + s * (x - p.re)
  let gu : ℝ → ℝ := fun x => p.im + (s + 1) * (x - p.re)
  have hinside := wedgeIn_graphRegion_east_lower_slope
    (a := p.re) (b := p.re + η) (f := fl) (g := gu)
    p dir η (s + 1) hd le_rfl hη le_rfl
    (by intro x hx; rfl) (by dsimp [s]; linarith)
    (by intro x hx; rfl)
  rcases hinside with ⟨δ, hδ, hmem⟩
  refine ⟨δ, hδ, ?_⟩
  intro a b f g hg t ε ht htd hε hεδ
  let z := wedgePoint p dir t ε
  have hz := hmem t ε ht htd hε hεδ
  change p.re < z.re ∧ z.re < p.re + η ∧
    fl z.re < z.im ∧ z.im < gu z.re at hz
  have hzIcc : z.re ∈ Icc p.re (p.re + η) := ⟨hz.1.le, hz.2.1.le⟩
  have htop := hg z.re hzIcc
  have hnot : z ∉ closedGraphRegion a b f g := by
    intro hclosed
    have hupper := hclosed.2.2.2
    rw [htop] at hupper
    exact (not_le_of_gt hz.2.2.1) hupper
  exact hnot

private theorem limitWedgePoint_neg (p dir : ℂ) (t ε : ℝ) :
    wedgePoint (-p) (-dir) t ε = -wedgePoint p dir t ε := by
  simp [wedgePoint]
  ring

/-- A fixed westward lower-boundary wedge radius works for every closed graph region
whose lower graph agrees locally with the dart segment. Helper toward adjudication n308; -/
theorem wedge_compl_closedGraphRegion_west_lower_uniform (p dir : ℂ) (η : ℝ)
    (hd : dir.re < 0) (hη : 0 < η) :
    ∃ δ > 0, ∀ (a b : ℝ) (f g : ℝ → ℝ),
      (∀ x ∈ Icc (p.re - η) p.re,
        f x = p.im + (dir.im / dir.re) * (x - p.re)) →
      ∀ t ε, 0 < t → t < δ → 0 < ε → ε < δ →
        wedgePoint p dir t ε ∉ closedGraphRegion a b f g := by
  have hd' : 0 < (-dir).re := by simpa using neg_pos.mpr hd
  have hright := wedge_compl_closedGraphRegion_east_upper_uniform
    (-p) (-dir) η hd' hη
  rcases hright with ⟨δ, hδ, hmem⟩
  refine ⟨δ, hδ, ?_⟩
  intro a b f g hf t ε ht htd hε hεδ
  let F : ℝ → ℝ := fun x => -g (-x)
  let G : ℝ → ℝ := fun x => -f (-x)
  have hratio : (-dir).im / (-dir).re = dir.im / dir.re := by
    simp [Complex.neg_re, Complex.neg_im]
  have hG : ∀ x ∈ Icc (-p).re ((-p).re + η),
      G x = (-p).im + ((-dir).im / (-dir).re) * (x - (-p).re) := by
    intro x hx
    have hy : -x ∈ Icc (p.re - η) p.re := by
      simp only [mem_Icc, Complex.neg_re] at hx ⊢
      constructor <;> linarith
    have hfx := hf (-x) hy
    change -f (-x) = _
    rw [hfx, hratio]
    simp only [Complex.neg_re, Complex.neg_im]
    ring
  let z := wedgePoint p dir t ε
  have hnot := hmem (-b) (-a) F G hG t ε ht htd hε hεδ
  rw [limitWedgePoint_neg] at hnot
  have hnot' : -z ∉ closedGraphRegion (-b) (-a) F G := by
    simpa [z] using hnot
  have hnotz : z ∉ closedGraphRegion a b f g := by
    intro hz
    have hneg : -z ∈ closedGraphRegion (-b) (-a) F G := by
      simp only [closedGraphRegion, Set.mem_ofPred_eq]
      rcases hz with ⟨hleft, hright, hlow, hhigh⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [Complex.neg_re] using neg_le_neg hright
      · simpa only [Complex.neg_re] using neg_le_neg hleft
      · simpa [F, Complex.neg_re, Complex.neg_im] using neg_le_neg hhigh
      · simpa [G, Complex.neg_re, Complex.neg_im] using neg_le_neg hlow
    exact hnot' hneg
  exact hnotz

private theorem monotoneLimit_layoutArc_stable {w : ℕ → Fin 3} {n m e : ℕ}
    (hnm : n ≤ m) (he : e < (kmswStage w n).nextEdge) :
    layoutArc w m e = layoutArc w n e := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [layoutArc_old w m e (he.trans_le (kmswStage_nextEdge_mono w hnm)), ih]

private theorem monotoneLimitStageRegion_subset_of_le {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (hnest : ∀ n, monotoneLimitStageRegion w Q G n ⊆
      monotoneLimitStageRegion w Q G (n + 1)) {m n : ℕ} (hmn : m ≤ n) :
    monotoneLimitStageRegion w Q G m ⊆ monotoneLimitStageRegion w Q G n := by
  induction hmn with
  | refl => exact subset_rfl
  | @step n hmn ih => exact ih.trans (hnest n)

private theorem monotoneLimit_upper_initialLine {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    {N m e : ℕ} (heN : e < (kmswStage w N).nextEdge)
    (hem : e < (kmswStage w m).nextEdge)
    (hUL : e ∈ (kmswStage w m).UL ++ (kmswStage w m).UR)
    (hstable : layoutArc w m e = layoutArc w N e) :
    ∀ x ∈ Icc (layoutArc w N e).start.re
      ((layoutArc w N e).start.re + (layoutArc w N e).initialDirection.re),
      (G m).upper x = (layoutArc w N e).start.im +
        ((layoutArc w N e).initialDirection.im /
          (layoutArc w N e).initialDirection.re) *
            (x - (layoutArc w N e).start.re) := by
  intro x hx
  let A := layoutArc w N e
  let p := A.start
  let v := A.point 1
  let dir := A.initialDirection
  let d : StageDart (kmswStage w m).nextEdge := (⟨e, hem⟩, false)
  have hArc : (Q m).arc d = A := by
    calc
      (Q m).arc d = layoutArc w m e := by simpa [d] using (G m).arc_layout d
      _ = A := hstable
  have hlen : 2 ≤ A.points.length := by
    rw [← hArc]
    exact (Q m).arc_length d
  have hmono : A.XMonotone := layoutArc_points_pairwise w N e heN
  have hdirpos : 0 < dir.re := by
    simpa [dir] using Polyline.initialDirection_re_pos hmono hlen
  have hdirRe : dir.re = v.re - p.re := by
    simp [dir, v, p, A, Polyline.initialDirection]
  have hdirIm : dir.im = v.im - p.im := by
    simp [dir, v, p, A, Polyline.initialDirection]
  have hpv : p.re < v.re := by linarith
  have hwidth : p.re + dir.re = v.re := by linarith
  have hx' : x ∈ Icc p.re v.re := by
    exact ⟨hx.1, by rw [← hwidth]; exact hx.2⟩
  let z : ℂ := ⟨x, segmentHeight p v x⟩
  have hzseg : z ∈ segment ℝ p v := by
    apply (mem_segment_iff_height hpv).2
    refine ⟨?_, ?_, ?_⟩
    · simpa [z] using hx'.1
    · simpa [z] using hx'.2
    · rfl
  have hzA : z ∈ A.image := by
    apply Or.inr
    refine ⟨0, by omega, ?_⟩
    change z ∈ segment ℝ (A.point 0) (A.point 1)
    rw [A.point_zero_eq_start]
    simpa [A, p, v] using hzseg
  have hzGraph : z ∈ graphOver (G m).xmin (G m).xmax (G m).upper := by
    rw [(G m).upper_trace]
    refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hUL, ?_⟩⟩
    simpa [stageEdgeTrace, hem, d, hArc] using hzA
  have hzFormula : z.im = p.im + (dir.im / dir.re) * (x - p.re) := by
    calc
      z.im = p.im + ((v.im - p.im) / (v.re - p.re)) * (x - p.re) := by
        simp [z, segmentHeight]
      _ = p.im + (dir.im / dir.re) * (x - p.re) := by
        rw [← hdirIm, ← hdirRe]
  calc
    (G m).upper x = z.im := by simpa [z] using hzGraph.2.2.symm
    _ = p.im + (dir.im / dir.re) * (x - p.re) := hzFormula

private theorem monotoneLimit_lower_initialLine {w : ℕ → Fin 3}
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    {N m e : ℕ} (heN : e < (kmswStage w N).nextEdge)
    (hem : e < (kmswStage w m).nextEdge)
    (hLL : e ∈ (kmswStage w m).LL ++ (kmswStage w m).LR)
    (hstable : layoutArc w m e = layoutArc w N e) :
    ∀ x ∈ Icc ((layoutArc w N e).reverse.start.re +
        (layoutArc w N e).reverse.initialDirection.re)
      (layoutArc w N e).reverse.start.re,
      (G m).lower x = (layoutArc w N e).reverse.start.im +
        ((layoutArc w N e).reverse.initialDirection.im /
          (layoutArc w N e).reverse.initialDirection.re) *
            (x - (layoutArc w N e).reverse.start.re) := by
  intro x hx
  let A := layoutArc w N e
  let B := A.reverse
  let p := B.start
  let v := B.point 1
  let dir := B.initialDirection
  let d : StageDart (kmswStage w m).nextEdge := (⟨e, hem⟩, false)
  have hArc : (Q m).arc d = A := by
    calc
      (Q m).arc d = layoutArc w m e := by simpa [d] using (G m).arc_layout d
      _ = A := hstable
  have hlen : 2 ≤ A.points.length := by
    rw [← hArc]
    exact (Q m).arc_length d
  have hmono : A.XMonotone := layoutArc_points_pairwise w N e heN
  have hdirneg : dir.re < 0 := by
    simpa [dir, B, A] using Polyline.reverse_initialDirection_re_neg hmono hlen
  have hdirRe : dir.re = v.re - p.re := by
    simp [dir, v, p, B, A, Polyline.initialDirection]
  have hdirIm : dir.im = v.im - p.im := by
    simp [dir, v, p, B, A, Polyline.initialDirection]
  have hpv : v.re < p.re := by linarith
  have hwidth : p.re + dir.re = v.re := by linarith
  have hx' : x ∈ Icc v.re p.re := by
    exact ⟨by rw [← hwidth]; exact hx.1, hx.2⟩
  let z : ℂ := ⟨x, segmentHeight v p x⟩
  have hzseg : z ∈ segment ℝ p v := by
    rw [segment_symm ℝ p v]
    apply (mem_segment_iff_height hpv).2
    refine ⟨?_, ?_, ?_⟩
    · simpa [z] using hx'.1
    · simpa [z] using hx'.2
    · rfl
  have hzA : z ∈ A.image := by
    apply Or.inr
    refine ⟨A.points.length - 2, by omega, ?_⟩
    have hidx : A.points.length - 2 + 1 = A.points.length - 1 := by omega
    change z ∈ segment ℝ (A.point (A.points.length - 2))
      (A.point (A.points.length - 2 + 1))
    rw [hidx, A.point_last_eq_finish]
    have hzseg' : z ∈ segment ℝ (A.point (A.points.length - 2)) A.finish := by
      rw [segment_symm ℝ (A.point (A.points.length - 2)) A.finish]
      simpa [B, p, v, Polyline.start_reverse, Polyline.reverse_point_one, hlen,
        A.point_last_eq_finish] using hzseg
    exact hzseg'
  have hzGraph : z ∈ graphOver (G m).xmin (G m).xmax (G m).lower := by
    rw [(G m).lower_trace]
    refine mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hLL, ?_⟩⟩
    simpa [stageEdgeTrace, hem, d, hArc] using hzA
  have hzFormula : z.im = p.im + (dir.im / dir.re) * (x - p.re) := by
    have hdirden : dir.re ≠ 0 := ne_of_lt hdirneg
    have hnum : p.im - v.im = -dir.im := by rw [hdirIm]; ring
    have hden : p.re - v.re = -dir.re := by rw [hdirRe]; ring
    have hratio : (p.im - v.im) / (p.re - v.re) = dir.im / dir.re := by
      rw [hnum, hden, neg_div_neg_eq]
    have hmul : (dir.im / dir.re) * dir.re = dir.im := by
      field_simp [hdirden]
    have hvIm : v.im = p.im + dir.im := by linarith [hdirIm]
    have hvRe : v.re = p.re + dir.re := by linarith [hdirRe]
    calc
      z.im = v.im + ((p.im - v.im) / (p.re - v.re)) * (x - v.re) := by
        simp [z, segmentHeight]
      _ = (p.im + dir.im) + (dir.im / dir.re) * (x - (p.re + dir.re)) := by
        rw [hratio, hvIm, hvRe]
      _ = p.im + (dir.im / dir.re) * (x - p.re) := by
        rw [show x - (p.re + dir.re) = (x - p.re) - dir.re by ring,
          mul_sub, hmul]
        ring
  calc
    (G m).lower x = z.im := by simpa [z] using hzGraph.2.2.symm
    _ = p.im + (dir.im / dir.re) * (x - p.re) := hzFormula





theorem monotoneLimit_cap_faces (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (hpos : ∀ n v, P.pos v.val = (Q n).pos v)
    (harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d)
    (hpersist : MonotoneLimitCapPersistence w Q G) :
    ∀ n i, ∃ F : P.Face,
      F.val = ((G n).cap i).region ∧ Bornology.IsBounded F.val := by
  intro n i
  let C := (G n).cap i
  have hc : IsPathConnected C.region :=
    isPathConnected_graphRegion C.ab C.low_continuous C.high_continuous C.separated
  obtain ⟨z, hz⟩ := hc.nonempty
  have havoid := cap_avoids_limitImage hfin Q G P hpos harc hpersist n i
  have hdisj : C.region ∩ P.image = ∅ :=
    disjoint_iff_inter_eq_empty.mp havoid
  have hzX : z ∉ P.image := (disjoint_left.mp havoid) hz
  have hcomp := connectedComponentIn_compl_eq_of_open_connected
      (isOpen_graphRegion C.low_continuous C.high_continuous)
      hc.isConnected hc.nonempty hdisj
      (cap_frontier_subset_limitImage (G n) P (harc n) i) hz
  refine ⟨⟨C.region, z, hzX, hcomp.symm⟩, rfl, ?_⟩
  exact isBounded_graphRegion C.low_continuous C.high_continuous cap_low_le_high






theorem monotoneLimit_faces_partition (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (hpos : ∀ n v, P.pos v.val = (Q n).pos v)
    (harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d)
    (hpersist : MonotoneLimitCapPersistence w Q G)
    (hEopen : IsOpen (monotoneLimitExteriorRegion w Q G))
    (hEconn : IsPathConnected (monotoneLimitExteriorRegion w Q G))
    (hEunb : ∀ R : ℝ, ∃ z ∈ monotoneLimitExteriorRegion w Q G, R < ‖z‖)
    (hEfront : frontier (monotoneLimitExteriorRegion w Q G) ⊆ P.image)
    (hEdisj : Disjoint (monotoneLimitExteriorRegion w Q G) P.image)
    (hcover : ∀ z ∉ P.image, z ∉ monotoneLimitExteriorRegion w Q G →
      ∃ n i, z ∈ ((G n).cap i).region) :
    ∃ U : P.Face,
      U.val = monotoneLimitExteriorRegion w Q G ∧
      P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      (∀ F : P.Face, F = U ∨ ∃ n i, F.val = ((G n).cap i).region) := by
  let E := monotoneLimitExteriorRegion w Q G
  obtain ⟨z, hzE, _⟩ := hEunb 0
  have hEcomp := connectedComponentIn_compl_eq_of_open_connected hEopen
    hEconn.isConnected ⟨z, hzE⟩ (disjoint_iff_inter_eq_empty.mp hEdisj)
    hEfront hzE
  have hzImage : z ∉ P.image := (disjoint_left.mp hEdisj) hzE
  let U : P.Face := ⟨E, z, hzImage, hEcomp.symm⟩
  have hUunb : P.IsUnbounded U := by
    intro R
    obtain ⟨x, hxE, hxR⟩ := hEunb R
    exact ⟨x, by simpa [U, E] using hxE, hxR⟩
  have hpartition (F : P.Face) :
      F = U ∨ ∃ n i, F.val = ((G n).cap i).region := by
    obtain ⟨x, hxImage, hxF⟩ := F.property
    have hxFmem : x ∈ F.val := by
      rw [hxF]
      exact mem_connectedComponentIn hxImage
    by_cases hxE : x ∈ E
    · left
      apply P.faces_eq_of_mem hxFmem
      change x ∈ E
      exact hxE
    · obtain ⟨n, i, hxCap⟩ := hcover x hxImage hxE
      obtain ⟨C, hC, _⟩ :=
        monotoneLimit_cap_faces w hfin Q G P hpos harc hpersist n i
      right
      refine ⟨n, i, ?_⟩
      have hxC : x ∈ C.val := by rw [hC]; exact hxCap
      have hFC := P.faces_eq_of_mem hxFmem hxC
      rw [hFC, hC]
  refine ⟨U, rfl, hUunb, ?_, hpartition⟩
  intro F hFunb
  rcases hpartition F with hFU | ⟨n, i, hFcap⟩
  · exact hFU
  · obtain ⟨C, hC, hCbdd⟩ :=
      monotoneLimit_cap_faces w hfin Q G P hpos harc hpersist n i
    have hFbounded : Bornology.IsBounded F.val := by
      rw [hFcap]
      simpa only [hC] using hCbdd
    obtain ⟨R, hball⟩ := hFbounded.subset_closedBall (0 : ℂ)
    obtain ⟨x, hxF, hxR⟩ := hFunb R
    have hxball : x ∈ Metric.closedBall (0 : ℂ) R := hball hxF
    have hxnorm : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxball
    exact False.elim ((not_lt_of_ge hxnorm) hxR)




theorem monotoneLimit_dartBorders_imp_limitExternalDart (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d)
    (U : P.Face) (hU : U.val = monotoneLimitExteriorRegion w Q G)
    (d : ℕ × Bool) : P.dartBorders d U → limitExternalDart w d := by
  change WedgeIn (P.arc d).start (P.arc d).initialDirection U.val → _
  rw [hU]
  intro hB
  by_contra hnot
  change ¬ ∃ N, ∀ n, N ≤ n →
    ∃ h : d.1 < (kmswStage w n).nextEdge,
      (kmswStageDirectedMap w n).IsOuter (⟨d.1, h⟩, d.2) at hnot
  push Not at hnot
  obtain ⟨n, hn, hno⟩ := hnot d.1
  have he : d.1 < (kmswStage w n).nextEdge :=
    (kmsw_edge_allocated_by_self w d.1).trans_le (kmswStage_nextEdge_mono w hn)
  let dN : StageDart (kmswStage w n).nextEdge := (⟨d.1, he⟩, d.2)
  obtain ⟨_, ⟨V, hV, _, _, hborder⟩⟩ := (G n).face_partition
  have hArcEq : P.arc d = (Q n).arc dN := by
    simpa [dN] using harc n dN
  obtain ⟨δ, hδ, hW⟩ := hB
  have hstageBorder : (Q n).dartBorders dN V := by
    change WedgeIn ((Q n).arc dN).start ((Q n).arc dN).initialDirection V.val
    refine ⟨δ, hδ, fun t ε ht htd he' he'd => ?_⟩
    let q := wedgePoint (P.arc d).start (P.arc d).initialDirection t ε
    have hqE : q ∈ monotoneLimitExteriorRegion w Q G := hW t ε ht htd he' he'd
    have hqNotR : q ∉ monotoneLimitStageRegion w Q G n := by
      change q ∉ ⋃ m, monotoneLimitStageRegion w Q G m at hqE
      exact fun hqR => hqE (mem_iUnion.mpr ⟨n, hqR⟩)
    have hqV : q ∈ V.val := by
      rw [hV]
      exact hqNotR
    simpa [q, wedgePoint, hArcEq] using hqV
  have houterN := (hborder dN).1 hstageBorder
  exact hno he houterN

/-- An eventually outer dart borders the limit exterior when the stage regions are
nested. Helper toward adjudication n308; not a paper result. See -/
theorem monotoneLimit_limitExternalDart_imp_dartBorders (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d)
    (U : P.Face) (hU : U.val = monotoneLimitExteriorRegion w Q G)
    (hnest : ∀ n, monotoneLimitStageRegion w Q G n ⊆
      monotoneLimitStageRegion w Q G (n + 1))
    (d : ℕ × Bool) : limitExternalDart w d → P.dartBorders d U := by
  intro hd
  rcases d with ⟨e, side⟩
  obtain ⟨N, hN⟩ := hd
  apply (dartBorders_iff_WedgeIn P (e, side) U).2
  rw [hU]
  cases side with
  | false =>
    have houterAt (m : ℕ) (hm : N ≤ m) :
        ∃ he : e < (kmswStage w m).nextEdge,
          (kmswStageDirectedMap w m).IsOuter (⟨e, he⟩, false) := by
      simpa using hN m hm
    obtain ⟨heN, houtN⟩ := houterAt N le_rfl
    let dN : StageDart (kmswStage w N).nextEdge := (⟨e, heN⟩, false)
    have hboundary (m : ℕ) (hm : N ≤ m) :
        e ∈ (kmswStage w m).UL ++ (kmswStage w m).UR := by
      obtain ⟨he, hout⟩ := houterAt m hm
      have hc := (kmswStage_isOuter_iff_boundary w m
        (⟨⟨e, he⟩, false⟩ : StageDart (kmswStage w m).nextEdge)).1 hout
      rcases hc with ⟨_, hUL⟩ | ⟨htrue, _⟩
      · exact hUL
      · cases htrue
    let A := layoutArc w N e
    have hQN : (Q N).arc dN = A := by
      simpa [dN, A] using (G N).arc_layout dN
    have hPArc : P.arc (e, false) = A := by
      calc
        P.arc (e, false) = (Q N).arc dN := by simpa [dN] using harc N dN
        _ = A := hQN
    have hlen : 2 ≤ A.points.length := by
      rw [← hQN]
      exact (Q N).arc_length dN
    have hmono : A.XMonotone := by
      exact layoutArc_points_pairwise w N e heN
    have hdirpos : 0 < A.initialDirection.re :=
      Polyline.initialDirection_re_pos hmono hlen
    obtain ⟨δ, hδ, havoid⟩ := wedge_compl_closedGraphRegion_east_upper_uniform
      A.start A.initialDirection A.initialDirection.re hdirpos hdirpos
    have havoidAt (m : ℕ) (hm : N ≤ m) (t ε : ℝ)
        (ht : 0 < t) (htd : t < δ) (hε : 0 < ε) (hεδ : ε < δ) :
        wedgePoint A.start A.initialDirection t ε ∉
          monotoneLimitStageRegion w Q G m := by
      obtain ⟨hem, _⟩ := houterAt m hm
      have hstable := monotoneLimit_layoutArc_stable hm heN
      have hline := monotoneLimit_upper_initialLine Q G heN hem
        (hboundary m hm) hstable
      change wedgePoint A.start A.initialDirection t ε ∉
        closedGraphRegion (G m).xmin (G m).xmax (G m).lower (G m).upper
      exact havoid (G m).xmin (G m).xmax (G m).lower (G m).upper hline
        t ε ht htd hε hεδ
    have havoidBefore (m : ℕ) (hm : ¬ N ≤ m) (t ε : ℝ)
        (ht : 0 < t) (htd : t < δ) (hε : 0 < ε) (hεδ : ε < δ) :
        wedgePoint A.start A.initialDirection t ε ∉
          monotoneLimitStageRegion w Q G m := by
      have hnotN := havoidAt N le_rfl t ε ht htd hε hεδ
      have hsub := monotoneLimitStageRegion_subset_of_le Q G hnest
        (Nat.le_of_not_ge hm)
      intro hmem
      exact hnotN (hsub hmem)
    refine ⟨δ, hδ, ?_⟩
    intro t ε ht htd hε hεδ
    have hnotUnion : wedgePoint A.start A.initialDirection t ε ∉
        ⋃ m, monotoneLimitStageRegion w Q G m := by
      intro hmem
      obtain ⟨m, hm⟩ := mem_iUnion.mp hmem
      by_cases hNm : N ≤ m
      · exact havoidAt m hNm t ε ht htd hε hεδ hm
      · exact havoidBefore m hNm t ε ht htd hε hεδ hm
    change wedgePoint (P.arc (e, false)).start
      (P.arc (e, false)).initialDirection t ε ∈
        monotoneLimitExteriorRegion w Q G
    simpa [A, hPArc, monotoneLimitExteriorRegion] using hnotUnion
  | true =>
    have houterAt (m : ℕ) (hm : N ≤ m) :
        ∃ he : e < (kmswStage w m).nextEdge,
          (kmswStageDirectedMap w m).IsOuter (⟨e, he⟩, true) := by
      simpa using hN m hm
    obtain ⟨heN, houtN⟩ := houterAt N le_rfl
    let dN : StageDart (kmswStage w N).nextEdge := (⟨e, heN⟩, true)
    have hboundary (m : ℕ) (hm : N ≤ m) :
        e ∈ (kmswStage w m).LL ++ (kmswStage w m).LR := by
      obtain ⟨he, hout⟩ := houterAt m hm
      have hc := (kmswStage_isOuter_iff_boundary w m
        (⟨⟨e, he⟩, true⟩ : StageDart (kmswStage w m).nextEdge)).1 hout
      rcases hc with ⟨hfalse, _⟩ | ⟨_, hLL⟩
      · cases hfalse
      · exact hLL
    let A := layoutArc w N e
    let B := A.reverse
    have hQN : (Q N).arc dN = B := by
      simpa [dN, A, B] using (G N).arc_layout dN
    have hPArc : P.arc (e, true) = B := by
      calc
        P.arc (e, true) = (Q N).arc dN := by simpa [dN] using harc N dN
        _ = B := hQN
    have hlenB : 2 ≤ B.points.length := by
      rw [← hQN]
      exact (Q N).arc_length dN
    have hlen : 2 ≤ A.points.length := by
      simpa [B, Polyline.reverse] using hlenB
    have hmono : A.XMonotone := layoutArc_points_pairwise w N e heN
    have hdirneg : B.initialDirection.re < 0 :=
      Polyline.reverse_initialDirection_re_neg hmono hlen
    let η := -B.initialDirection.re
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨δ, hδ, havoid⟩ := wedge_compl_closedGraphRegion_west_lower_uniform
      B.start B.initialDirection η hdirneg hη
    have hlineAt (m : ℕ) (hm : N ≤ m) :
        ∀ x ∈ Icc (B.start.re - η) B.start.re,
          (G m).lower x = B.start.im +
            (B.initialDirection.im / B.initialDirection.re) * (x - B.start.re) := by
      obtain ⟨hem, _⟩ := houterAt m hm
      have hstable := monotoneLimit_layoutArc_stable hm heN
      have hline := monotoneLimit_lower_initialLine Q G heN hem
        (hboundary m hm) hstable
      intro x hx
      have hx' : x ∈ Icc (B.start.re + B.initialDirection.re) B.start.re := by
        simpa [η] using hx
      simpa [B] using hline x hx'
    have havoidAt (m : ℕ) (hm : N ≤ m) (t ε : ℝ)
        (ht : 0 < t) (htd : t < δ) (hε : 0 < ε) (hεδ : ε < δ) :
        wedgePoint B.start B.initialDirection t ε ∉
          monotoneLimitStageRegion w Q G m := by
      change wedgePoint B.start B.initialDirection t ε ∉
        closedGraphRegion (G m).xmin (G m).xmax (G m).lower (G m).upper
      exact havoid (G m).xmin (G m).xmax (G m).lower (G m).upper
        (hlineAt m hm) t ε ht htd hε hεδ
    have havoidBefore (m : ℕ) (hm : ¬ N ≤ m) (t ε : ℝ)
        (ht : 0 < t) (htd : t < δ) (hε : 0 < ε) (hεδ : ε < δ) :
        wedgePoint B.start B.initialDirection t ε ∉
          monotoneLimitStageRegion w Q G m := by
      have hnotN := havoidAt N le_rfl t ε ht htd hε hεδ
      have hsub := monotoneLimitStageRegion_subset_of_le Q G hnest
        (Nat.le_of_not_ge hm)
      intro hmem
      exact hnotN (hsub hmem)
    refine ⟨δ, hδ, ?_⟩
    intro t ε ht htd hε hεδ
    have hnotUnion : wedgePoint B.start B.initialDirection t ε ∉
        ⋃ m, monotoneLimitStageRegion w Q G m := by
      intro hmem
      obtain ⟨m, hm⟩ := mem_iUnion.mp hmem
      by_cases hNm : N ≤ m
      · exact havoidAt m hNm t ε ht htd hε hεδ hm
      · exact havoidBefore m hNm t ε ht htd hε hεδ hm
    change wedgePoint (P.arc (e, true)).start
      (P.arc (e, true)).initialDirection t ε ∈
        monotoneLimitExteriorRegion w Q G
    simpa [B, hPArc, monotoneLimitExteriorRegion] using hnotUnion

/-- The exterior-face dart classification follows from the face partition and nested
stage regions. Helper toward adjudication n308; not a paper result. See -/
theorem monotoneLimit_dartBorders_iff (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (hpos : ∀ n v, P.pos v.val = (Q n).pos v)
    (harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d)
    (hpersist : MonotoneLimitCapPersistence w Q G)
    (hnest : ∀ n, monotoneLimitStageRegion w Q G n ⊆
      monotoneLimitStageRegion w Q G (n + 1))
    (hEopen : IsOpen (monotoneLimitExteriorRegion w Q G))
    (hEconn : IsPathConnected (monotoneLimitExteriorRegion w Q G))
    (hEunb : ∀ R : ℝ, ∃ z ∈ monotoneLimitExteriorRegion w Q G, R < ‖z‖)
    (hEfront : frontier (monotoneLimitExteriorRegion w Q G) ⊆ P.image)
    (hEdisj : Disjoint (monotoneLimitExteriorRegion w Q G) P.image)
    (hcover : ∀ z ∉ P.image, z ∉ monotoneLimitExteriorRegion w Q G →
      ∃ n i, z ∈ ((G n).cap i).region) :
    ∃ U : P.Face,
      U.val = monotoneLimitExteriorRegion w Q G ∧
      P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      (∀ F : P.Face, F = U ∨ ∃ n i, F.val = ((G n).cap i).region) ∧
      ∀ d, P.dartBorders d U ↔ limitExternalDart w d := by
  obtain ⟨U, hU, hUnb, huniq, hpartition⟩ :=
    monotoneLimit_faces_partition w hfin Q G P hpos harc hpersist hEopen hEconn
      hEunb hEfront hEdisj hcover
  refine ⟨U, hU, hUnb, huniq, hpartition, ?_⟩
  intro d
  exact ⟨monotoneLimit_dartBorders_imp_limitExternalDart w hfin Q G P harc U hU d,
    monotoneLimit_limitExternalDart_imp_dartBorders w hfin Q G P harc U hU hnest d⟩

end DirectedDistances.KMSW
