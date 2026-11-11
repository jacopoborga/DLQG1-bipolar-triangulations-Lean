/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.M0CutIdentificationAE
public import DirectedDistances.KMSW.M0CutLabelsOrder
public import DirectedDistances.KMSW.M0CutEdgeStatus
public import DirectedDistances.PaperProofs.Section1.BusemannM0Identified
public import DirectedDistances.PaperProofs.Section7.SDPTri

/-! Supporting lemmas for paper labels `lem-sdp-tri` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory Quiver DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section1





theorem m0CutData_rightBoundary_reachable (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (j - 1)))))
    {l k : ℤ} (hl : 0 ≤ l) (hlk : l < k) :
    m0CutReachable W H (m0CutData W H h hLL).seam
      ((m0CutData W H h hLL).x l) ((m0CutData W H h hLL).x k) := by
  let D := m0CutData W H h hLL
  have hstep (j : ℤ) (hj : 0 ≤ j) :
      m0CutDirectedStep W H D.seam (D.x j) (D.x (j + 1)) := by
    apply (m0Cut_directedStep_iff_present W H h hLL D.seam
      (m0Cut_seamEdge_iff W H h hLL) (D.x j) (D.x (j + 1))).mpr
    refine ⟨boundaryOuterEdge (shiftedStream W 0) h j,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h j).2.2.1 hj,
      ?_, ?_⟩
    · rw [← m0Cut_edgeWest W (boundaryOuterEdge (shiftedStream W 0) h j)]
      exact (m0CutData_x_order W H h hLL j).2.1
    · rw [← m0Cut_edgeEast W (boundaryOuterEdge (shiftedStream W 0) h j)]
      exact (m0CutData_x_order W H h hLL j).2.2
  have hlen (n : ℕ) :
      m0CutReachableLength (m0CutDirectedStep W H D.seam) n
        (D.x l) (D.x (l + (n : ℤ))) := by
    induction n with
    | zero => simp [m0CutReachableLength]
    | succ n ih =>
      change ∃ v, m0CutReachableLength (m0CutDirectedStep W H D.seam) n
        (D.x l) v ∧ m0CutDirectedStep W H D.seam v
          (D.x (l + ((n + 1 : ℕ) : ℤ)))
      refine ⟨D.x (l + (n : ℤ)), ih, ?_⟩
      have hindex : l + (n : ℤ) + 1 = l + ((n + 1 : ℕ) : ℤ) := by
        push_cast
        omega
      rw [← hindex]
      exact hstep (l + (n : ℤ)) (by omega)
  let n : ℕ := (k - l).toNat
  have hn : (n : ℤ) = k - l := by
    dsimp [n]
    exact Int.toNat_of_nonneg (by omega)
  have hp := hlen n
  rw [show l + (n : ℤ) = k by omega] at hp
  exact ⟨n, hp⟩




theorem m0CutData_rightBoundary_sdp_ne_top (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (j - 1)))))
    {l k : ℤ} (hl : 0 ≤ l) (hlk : l < k) :
    (m0CutData W H h hLL).sdp
      ((m0CutData W H h hLL).x l) ((m0CutData W H h hLL).x k) ≠ ⊤ := by
  exact m0CutData_sdp_ne_top_of_reachable W H h hLL
    ((m0CutData W H h hLL).x l) ((m0CutData W H h hLL).x k)
    (m0CutData_rightBoundary_reachable W H h hLL hl hlk)





theorem boundarySDPTriConclusion_iff_m0Cut (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (j - 1)))))
    (X : ℤ → ℤ) :
    (∀ l k : ℤ, 0 ≤ l → l < k →
      Reachable (boundaryPresentVertex (shiftedStream W 0) h l)
        (boundaryPresentVertex (shiftedStream W 0) h k) ∧
      X l - X k ≤
        ((sdp (boundaryPresentVertex (shiftedStream W 0) h l)
          (boundaryPresentVertex (shiftedStream W 0) h k)).toNat : ℤ)) ↔
    (∀ l k : ℤ, 0 ≤ l → l < k →
      m0CutReachable W H (m0CutData W H h hLL).seam
        ((m0CutData W H h hLL).x l) ((m0CutData W H h hLL).x k) ∧
      X l - X k ≤
        (((m0CutData W H h hLL).sdp
          ((m0CutData W H h hLL).x l)
          ((m0CutData W H h hLL).x k)).toNat : ℤ)) := by
  constructor
  · intro htri l k hl hlk
    have hr := m0CutData_rightBoundary_reachable W H h hLL hl hlk
    have heq := m0Cut_identification_boundary_sdp W H h hLL l k
    refine ⟨hr, ?_⟩
    have hineq := (htri l k hl hlk).2
    rw [← heq] at hineq
    exact hineq
  · intro htri l k hl hlk
    have hcut := htri l k hl hlk
    have hr : Reachable (boundaryPresentVertex (shiftedStream W 0) h l)
        (boundaryPresentVertex (shiftedStream W 0) h k) := by
      change Reachable (⟨boundaryVertex (shiftedStream W 0) h l⟩ :
        PresentVertex (shiftedStream W 0))
        ⟨boundaryVertex (shiftedStream W 0) h k⟩
      rw [(m0CutData W H h hLL).x_eq h hLL l,
        (m0CutData W H h hLL).x_eq h hLL k] at hcut
      exact (m0Cut_reachable_iff_present W H h hLL
        (m0CutData W H h hLL).seam
        (m0Cut_seamEdge_iff W H h hLL)
        (boundaryVertex (shiftedStream W 0) h l)
        (boundaryVertex (shiftedStream W 0) h k)).mp hcut.1
    have heq := m0Cut_identification_boundary_sdp W H h hLL l k
    refine ⟨hr, ?_⟩
    have hineq := hcut.2
    rw [heq] at hineq
    exact hineq






theorem sdp_tri_identified_ae :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ j, D.x j = V (boundaryVertex w h j)) ∧
        (D.rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          D.rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W D.rootDart.1 = D.x 0 ∧
          wholePlaneEdgeEast W D.rootDart.1 = D.x 1 ∧
          wholePlaneEdgePresent W D.rootDart.1 ∧ D.tail D.rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ j : ℤ, j ≤ -1 ∧ e = boundaryOuterEdge w h j)) ∧
        (∀ e, D.missing (E e) ↔
          ∃ j : ℤ, j ≤ -1 ∧ e = boundaryOuterEdge w h j) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧
            V (edgeEast w e) = V b) ∧
        (∀ a b, D.sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, D.ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ j j', D.sdp (D.x j) (D.x j') =
          DirectedDistances.sdp (boundaryPresentVertex w h j)
            (boundaryPresentVertex w h j')) ∧
        (∀ j j', D.ldp (D.x j) (D.x j') =
          presentLdp (boundaryPresentVertex w h j) (boundaryPresentVertex w h j'))) ∧
      (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
      ∀ X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X →
        ∀ l k : ℤ, 0 ≤ l → l < k →
          m0CutReachable W H D.seam (D.x l) (D.x k) ∧
          D.sdp (D.x l) (D.x k) ≠ ⊤ ∧
          X l - X k ≤ ((D.sdp (D.x l) (D.x k)).toNat : ℤ) := by
  have htriCode := DirectedDistances.PaperProofs.Section7.lem_sdp_tri
  rw [← RandomWalk.wholePlaneIIDCodeMeasure_map_shiftedPath 0] at htriCode
  have htriMap := ae_of_ae_map
    (RandomWalk.measurable_shiftedCodePath 0).aemeasurable htriCode
  filter_upwards [htriMap,
    DirectedDistances.PaperProofs.Section1.m0Cut_busemann_identified_ae]
    with W htri hbusemann
  have hpath : (fun i => RandomWalk.shiftedCodePath W 0 (i + 1)) =
      shiftedStream W 0 := by
    funext i
    simp [RandomWalk.shiftedCodePath]
  rw [hpath] at htri
  obtain ⟨H, h, hLL, hid, hSDP, _hLDP⟩ := hbusemann
  let D := m0CutData W H h hLL
  refine ⟨H, h, hLL, ?_, ?_, ?_⟩
  · exact hid
  · exact hSDP
  · intro X hX l k hl hlk
    have hXboundary :
        IsBoundaryBusemannSDP (boundaryPresentVertex (shiftedStream W 0) h) X :=
      (boundaryBusemannSDP_iff_identified W H h hLL X).mpr hX
    have hcarrier := htri h X hXboundary l k hl hlk
    have hreach := m0CutData_rightBoundary_reachable W H h hLL hl hlk
    have hfinite := m0CutData_rightBoundary_sdp_ne_top W H h hLL hl hlk
    have heq := m0Cut_identification_boundary_sdp W H h hLL l k
    refine ⟨hreach, hfinite, ?_⟩
    have hineq := hcarrier.2
    rw [← heq] at hineq
    exact hineq

end DirectedDistances.PaperProofs.Section7
