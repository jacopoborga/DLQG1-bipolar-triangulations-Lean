module

public import DirectedDistances.PlanarMap.GraphRegion
public import DirectedDistances.KMSW.KMSWStageDrawing
public import DirectedDistances.KMSW.KMSWStageZeroDrawing

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open Set
open scoped Topology



structure GraphCap where
  a : ℝ
  b : ℝ
  low : ℝ → ℝ
  high : ℝ → ℝ
  ab : a < b
  low_continuous : ContinuousOn low (Icc a b)
  high_continuous : ContinuousOn high (Icc a b)
  separated : ∀ x ∈ Ioo a b, low x < high x
  left_join : low a = high a
  right_join : low b = high b

namespace GraphCap

/-- The open region between the cap's two graphs. See `def-kmsw`, -/
@[expose] def region (C : GraphCap) : Set ℂ :=
  graphRegion C.a C.b C.low C.high

end GraphCap

/-- The point in the left wedge at distance parameter `t` and slope `ε`.
This is the exact wedge shape in `PlaneRealization.lean:174-178` and the -/
@[expose] def wedgePoint (p dir : ℂ) (t ε : ℝ) : ℂ :=
  p + (t : ℂ) * (dir + (ε : ℂ) * Complex.I * dir)

/-- Uniform small left-wedge membership, matching `dartBorders` in -/
@[expose] def WedgeIn (p dir : ℂ) (S : Set ℂ) : Prop :=
  ∃ δ > 0, ∀ t ε, 0 < t → t < δ → 0 < ε → ε < δ →
    wedgePoint p dir t ε ∈ S



theorem dartBorders_iff_WedgeIn {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face) :
    P.dartBorders d F ↔
      WedgeIn (P.arc d).start (P.arc d).initialDirection F.val := Iff.rfl




structure MonotoneStageCertificate (w : ℕ → Fin 3) (n : ℕ)
    (P : StageDrawing w n) where
  xmin : ℝ
  xmax : ℝ
  hx : xmin ≤ xmax
  lower : ℝ → ℝ
  upper : ℝ → ℝ
  lower_continuous : ContinuousOn lower (Icc xmin xmax)
  upper_continuous : ContinuousOn upper (Icc xmin xmax)
  lower_le_upper : ∀ x ∈ Icc xmin xmax, lower x ≤ upper x
  lower_trace : graphOver xmin xmax lower =
    ⋃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR, stageEdgeTrace P e
  upper_trace : graphOver xmin xmax upper =
    ⋃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR, stageEdgeTrace P e
  cap : Fin (kmswStage w n).triangles.length → GraphCap
  capLower : Fin (kmswStage w n).triangles.length → List ℕ
  capUpper : Fin (kmswStage w n).triangles.length → List ℕ
  cap_lower_trace : ∀ i, graphOver (cap i).a (cap i).b (cap i).low =
    ⋃ e ∈ capLower i, stageEdgeTrace P e
  cap_upper_trace : ∀ i, graphOver (cap i).a (cap i).b (cap i).high =
    ⋃ e ∈ capUpper i, stageEdgeTrace P e
  cap_edges : ∀ i e, e ∈ capLower i ++ capUpper i ↔
    e = ((kmswStage w n).triangles.get i).1 ∨
      e = ((kmswStage w n).triangles.get i).2.1 ∨
      e = ((kmswStage w n).triangles.get i).2.2
  cap_avoid : ∀ i, Disjoint (cap i).region P.image
  cap_disjoint : ∀ i j, i ≠ j → Disjoint (cap i).region (cap j).region
  cover : P.image ∪ ⋃ i, closure (cap i).region =
    closedGraphRegion xmin xmax lower upper
  cap_lower_wedge : ∀ i e (h : e < (kmswStage w n).nextEdge),
    e ∈ capLower i →
      WedgeIn (P.arc ((⟨e, h⟩, false) : StageDart (kmswStage w n).nextEdge)).start
        (P.arc ((⟨e, h⟩, false) : StageDart (kmswStage w n).nextEdge)).initialDirection
        (cap i).region
  cap_upper_wedge : ∀ i e (h : e < (kmswStage w n).nextEdge),
    e ∈ capUpper i →
      WedgeIn (P.arc ((⟨e, h⟩, true) : StageDart (kmswStage w n).nextEdge)).start
        (P.arc ((⟨e, h⟩, true) : StageDart (kmswStage w n).nextEdge)).initialDirection
        (cap i).region
  ext_upper_wedge : ∀ e (h : e < (kmswStage w n).nextEdge),
    e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR →
      WedgeIn
        (P.arc ((⟨e, h⟩, false) : StageDart (kmswStage w n).nextEdge)).start
        (P.arc ((⟨e, h⟩, false) : StageDart (kmswStage w n).nextEdge)).initialDirection
        (closedGraphRegion xmin xmax lower upper)ᶜ
  ext_lower_wedge : ∀ e (h : e < (kmswStage w n).nextEdge),
    e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR →
      WedgeIn
        (P.arc ((⟨e, h⟩, true) : StageDart (kmswStage w n).nextEdge)).start
        (P.arc ((⟨e, h⟩, true) : StageDart (kmswStage w n).nextEdge)).initialDirection
        (closedGraphRegion xmin xmax lower upper)ᶜ

private theorem initialPolyline_image (a b : ℂ) :
    (⟨[a, b], by simp⟩ : Polyline).image = segment ℝ a b := by
  ext z
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · subst z
      exact left_mem_segment ℝ a b
    · have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
      subst i
      exact hz
  · intro hz
    exact Or.inr ⟨0, by change 1 < 2; omega, hz⟩



theorem stage0_edge_trace (w : ℕ → Fin 3) :
    stageEdgeTrace (kmswStage0Drawing w) 0 = segment ℝ (0 : ℂ) 1 := by
  simp [stageEdgeTrace, kmswStage, kmswInit, kmswStage0Drawing,
    kmswStage0Arc, initialPolyline_image]



theorem graphOver_zero_eq_segment :
    graphOver 0 1 (fun _ : ℝ => 0) = segment ℝ (0 : ℂ) 1 := by
  rw [graphOver_eq_image, segment_eq_image']
  congr 1
  funext x
  simp [graphParam]



theorem closedGraphRegion_zero_eq_segment :
    closedGraphRegion 0 1 (fun _ : ℝ => 0) (fun _ : ℝ => 0) =
      segment ℝ (0 : ℂ) 1 := by
  have hregion : closedGraphRegion 0 1 (fun _ : ℝ => 0) (fun _ : ℝ => 0) =
      graphOver 0 1 (fun _ : ℝ => 0) := by
    ext z
    constructor
    · rintro ⟨hx₀, hx₁, him₀, him₁⟩
      exact ⟨hx₀, hx₁, le_antisymm him₁ him₀⟩
    · rintro ⟨hx₀, hx₁, him⟩
      change z.im = 0 at him
      exact ⟨hx₀, hx₁, by simp [him], by simp [him]⟩
  rw [hregion, graphOver_zero_eq_segment]



theorem stage0_upper_wedge :
    WedgeIn (0 : ℂ) 1
      (closedGraphRegion 0 1 (fun _ : ℝ => 0) (fun _ : ℝ => 0))ᶜ := by
  refine ⟨1, by norm_num, ?_⟩
  intro t ε ht _ hε _
  change wedgePoint 0 1 t ε ∉
    closedGraphRegion 0 1 (fun _ : ℝ => 0) (fun _ : ℝ => 0)
  intro hz
  have him : 0 < (wedgePoint 0 1 t ε).im := by
    simp [wedgePoint]
    exact mul_pos ht hε
  exact (not_le_of_gt him) (by simpa [closedGraphRegion] using hz.2.2.2)



theorem stage0_lower_wedge :
    WedgeIn (1 : ℂ) (-1)
      (closedGraphRegion 0 1 (fun _ : ℝ => 0) (fun _ : ℝ => 0))ᶜ := by
  refine ⟨1, by norm_num, ?_⟩
  intro t ε ht _ hε _
  change wedgePoint 1 (-1) t ε ∉
    closedGraphRegion 0 1 (fun _ : ℝ => 0) (fun _ : ℝ => 0)
  intro hz
  have him : (wedgePoint 1 (-1) t ε).im < 0 := by
    simp [wedgePoint]
    exact mul_pos ht hε
  exact (not_le_of_gt him) (by simpa [closedGraphRegion] using hz.2.2.1)




@[expose] noncomputable def kmswStage0MonotoneCertificate
    (w : ℕ → Fin 3) :
    MonotoneStageCertificate w 0 (kmswStage0Drawing w) := by
  refine
    { xmin := 0
      xmax := 1
      hx := by norm_num
      lower := fun _ => 0
      upper := fun _ => 0
      lower_continuous := continuousOn_const
      upper_continuous := continuousOn_const
      lower_le_upper := by intro x hx; rfl
      lower_trace := ?_
      upper_trace := ?_
      cap := fun i => Fin.elim0 i
      capLower := fun i => Fin.elim0 i
      capUpper := fun i => Fin.elim0 i
      cap_lower_trace := ?_
      cap_upper_trace := ?_
      cap_edges := ?_
      cap_avoid := ?_
      cap_disjoint := ?_
      cover := ?_
      cap_lower_wedge := ?_
      cap_upper_wedge := ?_
      ext_upper_wedge := ?_
      ext_lower_wedge := ?_ }
  · simp [kmswStage, kmswInit, graphOver_zero_eq_segment, stage0_edge_trace]
  · simp [kmswStage, kmswInit, graphOver_zero_eq_segment, stage0_edge_trace]
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i e
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i j hij
    exact Fin.elim0 i
  · simp [kmswStage, kmswInit, closedGraphRegion_zero_eq_segment]
    convert kmswStage0Drawing_image w using 1
    rfl
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro e h he
    have he0 : e = 0 := by simpa [kmswStage, kmswInit] using he
    subst e
    simpa [kmswStage0Drawing, kmswStage0Arc, Polyline.start,
      Polyline.initialDirection, Polyline.point] using stage0_upper_wedge
  · intro e h he
    have he0 : e = 0 := by simpa [kmswStage, kmswInit] using he
    subst e
    simpa [kmswStage0Drawing, kmswStage0Arc, Polyline.start,
      Polyline.initialDirection, Polyline.point] using stage0_lower_wedge

end DirectedDistances.KMSW
