/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLeftmostNonCrossing2

/-! # Leftmost non-crossing for adjacent geodesic slices -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

private theorem m0Cut_graphRay_epigraph_closed
    {x₀ : ℝ} {X : WithTop ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (rayDomain x₀ X))
    (hesc : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ X,
      ∀ t ∈ rayDomain x₀ X, a ≤ t → M ≤ g t) :
    IsClosed {q : ℂ | q.re ∈ rayDomain x₀ X ∧ g q.re ≤ q.im} := by
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hre := (Complex.continuous_re.tendsto z).comp hz
  have him := (Complex.continuous_im.tendsto z).comp hz
  obtain ⟨M, hM⟩ := him.bddAbove_range
  obtain ⟨a, ha, hbig⟩ := hesc (M + 1)
  have hlt : ∀ n, (u n).re < a := by
    intro n
    by_contra hn
    have h₁ := hbig _ (hu n).1 (le_of_not_gt hn)
    have h₂ := (hu n).2
    have h₃ := hM (Set.mem_range_self n)
    change (u n).im ≤ M at h₃
    linarith only [h₁, h₂, h₃]
  have hza : z.re ≤ a := le_of_tendsto' hre (fun n => (hlt n).le)
  have hzx : x₀ ≤ z.re := ge_of_tendsto' hre (fun n => (hu n).1.1)
  have hzd : z.re ∈ rayDomain x₀ X :=
    ⟨hzx, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hza) ha.2⟩
  refine ⟨hzd, ?_⟩
  have hlim := (hg z.re hzd).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr
      ⟨hre, Filter.Eventually.of_forall (fun n => (hu n).1)⟩)
  exact le_of_tendsto_of_tendsto' hlim him (fun n => (hu n).2)

private theorem m0Cut_graphRay_hypograph_closed
    {x₀ : ℝ} {X : WithTop ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (rayDomain x₀ X)) :
    IsClosed {q : ℂ | x₀ ≤ q.re ∧
      (q.re ∈ rayDomain x₀ X → q.im ≤ g q.re)} := by
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hre := (Complex.continuous_re.tendsto z).comp hz
  have him := (Complex.continuous_im.tendsto z).comp hz
  refine ⟨ge_of_tendsto' hre (fun n => (hu n).1), ?_⟩
  intro hzd
  have hev : ∀ᶠ n in Filter.atTop, (u n).re ∈ rayDomain x₀ X := by
    induction X using WithTop.recTopCoe with
    | top =>
      exact Filter.Eventually.of_forall (fun n => ⟨(hu n).1, WithTop.coe_lt_top _⟩)
    | coe b =>
      have hzb : z.re < b := WithTop.coe_lt_coe.mp hzd.2
      exact (hre.eventually (gt_mem_nhds hzb)).mono
        (fun n hn => ⟨(hu n).1, WithTop.coe_lt_coe.mpr hn⟩)
  have hlim := (hg z.re hzd).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hre, hev⟩)
  exact le_of_tendsto_of_tendsto him hlim (hev.mono (fun n hn => (hu n).2 hn))



theorem m0Cut_next_boundary_mem_right_side {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL (k - 1) longest) :
    boundaryVertex (shiftedStream W 0) h k ∈
      m0GeodesicSideVertices hp P .right := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let f := seamFun (shiftedStream W 0) h (H.1 0)
  let x₀ := (monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))).pos
      (boundaryVertex (shiftedStream W 0) h (k - 1)) |>.re
  let a := seamX (shiftedStream W 0) h (H.1 0) ((k - 1) - 1)
  let z : ℂ := ⟨seamX (shiftedStream W 0) h (H.1 0) k,
    f (seamX (shiftedStream W 0) h (H.1 0) k)⟩
  have hpos (j : ℤ) : G.pos ((m0CutData W H h hLL).x j) =
      (⟨seamX (shiftedStream W 0) h (H.1 0) j,
        f (seamX (shiftedStream W 0) h (H.1 0) j)⟩ : ℂ) := by
    rw [(m0CutData W H h hLL).x_eq h hLL j, m0Geodesic_pos_runZero hp]
    exact boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) j
  have hx₀ : x₀ = seamX (shiftedStream W 0) h (H.1 0) (k - 1) := by
    dsimp [x₀]
    simpa using congrArg Complex.re
      (boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) (k - 1))
  change G.pos (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)) ∈
    m0GeodesicSideRegion hp P .right
  rw [show G.pos (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)) = z by
    rw [← (m0CutData W H h hLL).x_eq h hLL k, hpos]]
  refine ⟨?_, ?_⟩
  · change f z.re ≤ z.im
    rfl
  · intro hzleft
    obtain ⟨X, g, hxX, hg, hgraph, hesc⟩ := m0GeodesicTrace_properGraphRay hp P
    have hroot : (⟨x₀, f x₀⟩ : ℂ) ∈ m0GeodesicTrace hp P := by
      have hroot' := m0Geodesic_root_pos_mem_trace hp P
      rw [hpos (k - 1)] at hroot'
      have heq : (⟨x₀, f x₀⟩ : ℂ) =
          (⟨seamX (shiftedStream W 0) h (H.1 0) (k - 1),
            f (seamX (shiftedStream W 0) h (H.1 0) (k - 1))⟩ : ℂ) := by
        rw [hx₀]
      exact heq ▸ hroot'
    have hrootGraph : (⟨x₀, f x₀⟩ : ℂ) ∈
        {q : ℂ | q.re ∈ rayDomain x₀ X ∧ q.im = g q.re} := by
      rw [← hgraph]
      exact hroot
    let U : Set ℂ := {q | q.re ≤ x₀} ∪
      {q | q.re ∈ rayDomain x₀ X ∧ g q.re ≤ q.im}
    let D : Set ℂ := {q | x₀ ≤ q.re ∧
      (q.re ∈ rayDomain x₀ X → q.im ≤ g q.re)}
    have hU : IsClosed U :=
      (isClosed_Iic.preimage Complex.continuous_re).union
        (m0Cut_graphRay_epigraph_closed hg hesc)
    have hD : IsClosed D := m0Cut_graphRay_hypograph_closed hg
    have hcover : (Set.univ : Set ℂ) ⊆ U ∪ D := by
      intro q _
      by_cases hq : q.re ≤ x₀
      · exact Or.inl (Or.inl hq)
      · by_cases hd : q.re ∈ rayDomain x₀ X
        · by_cases hh : g q.re ≤ q.im
          · exact Or.inl (Or.inr ⟨hd, hh⟩)
          · exact Or.inr ⟨(lt_of_not_ge hq).le,
              fun _ => (lt_of_not_ge hh).le⟩
        · exact Or.inr ⟨(lt_of_not_ge hq).le, fun hh => (hd hh).elim⟩
    have hbase : (⟨a, f a⟩ : ℂ) ∈
        m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
      have hbase' := m0Geodesic_previous_pos_mem_complement hp P
      have heq : G.pos ((m0CutData W H h hLL).x ((k - 1) - 1)) =
          (⟨a, f a⟩ : ℂ) := by
        simpa only [a] using hpos ((k - 1) - 1)
      exact heq ▸ hbase'
    have hzleft' : z ∈ connectedComponentIn
        (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P)
        (⟨a, f a⟩ : ℂ) := by
      change z ∈ connectedComponentIn
        (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P)
        (G.pos ((m0CutData W H h hLL).x ((k - 1) - 1))) at hzleft
      rw [hpos ((k - 1) - 1)] at hzleft
      simpa only [a] using hzleft
    have ha : a < x₀ := by
      dsimp [a, x₀]
      exact seamX_strictMono (shiftedStream W 0) h (H.1 0) (by omega)
    have hzD : z ∈ D := by
      refine ⟨?_, ?_⟩
      · change x₀ ≤ seamX (shiftedStream W 0) h (H.1 0) k
        rw [hx₀]
        exact (seamX_strictMono (shiftedStream W 0) h (H.1 0) (by omega)).le
      · intro hdom
        have htrace : (⟨z.re, g z.re⟩ : ℂ) ∈ m0GeodesicTrace hp P := by
          rw [hgraph]
          exact ⟨hdom, rfl⟩
        have hamb := m0GeodesicTrace_subset_ambient hp P htrace
        change f z.re ≤ g z.re at hamb
        simpa [z] using hamb
    have hsplit := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn
      U D hU hD
      (fun q _ => hcover (Set.mem_univ q))
      ⟨⟨a, f a⟩, mem_connectedComponentIn hbase, Or.inl ha.le⟩
      ⟨z, hzleft', hzD.1, hzD.2⟩
    obtain ⟨q, hqC, hqU, hqD⟩ := hsplit
    have hq := connectedComponentIn_subset _ _ hqC
    apply hq.2
    rw [hgraph]
    rcases hqU with hqw | hqu
    · have heq : q.re = x₀ := le_antisymm hqw hqD.1
      have hdom : q.re ∈ rayDomain x₀ X := heq ▸ hrootGraph.1
      refine ⟨hdom, le_antisymm (hqD.2 hdom) ?_⟩
      have hf : f q.re ≤ q.im := hq.1
      rw [heq] at hf ⊢
      rw [← hrootGraph.2]
      exact hf
    · exact ⟨hqu.1, le_antisymm (hqD.2 hqu.1) hqu.2⟩



















end DirectedDistances.PaperProofs.Section5
