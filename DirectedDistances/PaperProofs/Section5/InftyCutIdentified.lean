module

public import DirectedDistances.PaperProofs.Section5.InftyCutCarrierEvent
public import DirectedDistances.KMSW.M0CutIdentificationAE
public import DirectedDistances.KMSW.M0CutPathVisit

/-! Supporting lemmas for paper labels `lem-infty-cut` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Quiver DirectedDistances.KMSW
open DirectedDistances.RandomWalk





theorem lem_infty_cut_identified :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let E := wholePlaneEdgeι W 0
      let D := m0CutData W H h hLL
      (Function.Injective V ∧
      Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
      Function.Injective E ∧
      Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
      (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
      ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
        (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
        wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
        wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
        wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
      (∀ e, EdgePresent w e ↔
        (wholePlaneEdgePresent W (E e) ∧
          ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
      (∀ e, (D).missing (E e) ↔
        ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
      (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
        ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
      (∀ a b, (D).sdp (V a) (V b) =
        DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
      (∀ k k', (D).sdp ((D).x k) ((D).x k') =
        DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
      (∀ k k', (D).ldp ((D).x k) ((D).x k') =
        presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
      ∀ k k' : ℤ, k < k' →
        ∃ v : ℕ → WholePlaneVertex W,
          Function.Injective v ∧
          (∀ m, v m ∈ m0CutLeftVertices W H D.seam) ∧
          ∀ ell : ℤ, ell ∈ Set.Icc k k' →
            ∀ y : ℕ → WholePlaneVertex W,
              Function.Injective y →
              (∀ j, m0CutReachable W H D.seam (D.x ell) (y j)) →
              ∀ m, ∃ J, ∀ j, J ≤ j →
                ∀ n : ℕ, ∀ p : Fin (n + 1) → WholePlaneVertex W,
                  p 0 = D.x ell →
                  p (Fin.last n) = y j →
                  (∀ i : Fin n,
                    m0CutDirectedStep W H D.seam
                      (p i.castSucc) (p i.succ)) →
                  ∃ i, p i = v m := by
  have hcarrier := iidCodes_ae_lem_infty_cut_carrier
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hcarrier
  have hcarrierMap := ae_of_ae_map
    (measurable_shiftedCodePath 0).aemeasurable hcarrier
  filter_upwards [hcarrierMap, m0Cut_identification_ae] with W hcut hid
  have hpath :
      (fun i => shiftedCodePath W 0 (i + 1)) = shiftedStream W 0 := by
    funext i
    simp [shiftedCodePath]
  rw [hpath] at hcut
  obtain ⟨hfin, hc, _hgeometry, _hcarrier, hsequence⟩ := hcut
  obtain ⟨H, h, hLL, _hid⟩ := hid
  have hhc : hc = h := Subsingleton.elim _ _
  subst hc
  let D := m0CutData W H h hLL
  have hvertices := m0Cut_identification_vertices W H h hLL
  have hVin : Function.Injective (wholePlaneVertexι W 0) := hvertices.1
  have hVrange :
      Set.range (wholePlaneVertexι W 0) = m0CutLeftVertices W H D.seam := by
    exact hvertices.2
  refine ⟨H, h, hLL, ?_⟩
  intro w V E Dcut
  refine ⟨_hid, ?_⟩
  intro k k' hkk
  obtain ⟨u, hu, hwindow⟩ := hsequence k k' hkk
  refine ⟨fun m => wholePlaneVertexι W 0 (u m).id, ?_, ?_, ?_⟩
  · intro m n hmn
    have huEq : u m = u n := by
      cases um : u m with
      | mk aid =>
        cases un : u n with
        | mk bid =>
          have hid : aid = bid := by
            apply hVin
            simpa [um, un] using hmn
          subst bid
          rfl
    exact hu huEq
  · intro m
    rw [← hVrange]
    exact ⟨(u m).id, rfl⟩
  · intro ell hell y hy hreach m
    have htarget : ∀ j, ∃ b : ℕ,
        wholePlaneVertexι W 0 b = y j := by
      intro j
      have hreach' : m0CutReachable W H D.seam
          (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h ell))
          (y j) := by
        rw [← D.x_eq h hLL ell]
        exact hreach j
      exact m0Cut_reachable_target_is_vertex W H h hLL D.seam
        (m0Cut_seamEdge_iff W H h hLL) hreach'
    choose b hb using htarget
    have hb_inj : Function.Injective b := by
      intro i j hij
      apply hy
      calc
        y i = wholePlaneVertexι W 0 (b i) := (hb i).symm
        _ = wholePlaneVertexι W 0 (b j) := congrArg _ hij
        _ = y j := hb j
    have hpresent : ∀ j, Quiver.Reachable
        (boundaryPresentVertex (shiftedStream W 0) h ell)
        (⟨b j⟩ : PresentVertex (shiftedStream W 0)) := by
      intro j
      have hr : m0CutReachable W H D.seam
          (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h ell))
          (wholePlaneVertexι W 0 (b j)) := by
        rw [← D.x_eq h hLL ell, hb j]
        exact hreach j
      exact (m0Cut_reachable_iff_present W H h hLL D.seam
        (m0Cut_seamEdge_iff W H h hLL)
        (boundaryVertex (shiftedStream W 0) h ell) (b j)).mp hr
    obtain ⟨J, hJ⟩ := hwindow ell hell (fun j => (⟨b j⟩ :
      PresentVertex (shiftedStream W 0)))
      (fun i j hij => by
        have hij' : (⟨b i⟩ : PresentVertex (shiftedStream W 0)) = ⟨b j⟩ := by
          simpa using hij
        exact hb_inj (congrArg PresentVertex.id hij')) hpresent m
    refine ⟨J, ?_⟩
    intro j hj n p hp0 hpend hsteps
    have hvisit : ∀ n (p : Fin (n + 1) → WholePlaneVertex W),
        p 0 = wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h ell) →
        p (Fin.last n) = wholePlaneVertexι W 0 (b j) →
        (∀ i : Fin n,
          m0CutDirectedStep W H D.seam (p i.castSucc) (p i.succ)) →
        ∃ i, p i = wholePlaneVertexι W 0 (u m).id :=
      (m0Cut_visit_iff W H h hLL (boundaryVertex (shiftedStream W 0) h ell)
        (b j) (u m).id).2 (hJ j hj)
    have hp0' : p 0 = wholePlaneVertexι W 0
        (boundaryVertex (shiftedStream W 0) h ell) := by
      exact hp0.trans (D.x_eq h hLL ell)
    have hpend' : p (Fin.last n) = wholePlaneVertexι W 0 (b j) := by
      exact hpend.trans (hb j).symm
    exact hvisit n p hp0' hpend' hsteps

end DirectedDistances.PaperProofs.Section5
