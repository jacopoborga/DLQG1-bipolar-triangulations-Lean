module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmap

/-! Infinite directed rays from the future-copy boundary in Lemma 5.10

The statements retain edge IDs in the incidence carriers. The future boundary index `j ≤ 0`
corresponds to the source boundary label `xᵇᶜ_{k+j}` by
`ae_uibhbotFutureBoundary_index`. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory Quiver
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section5

private theorem future_pathEdges_cast_start {W : ℤ → Fin 3}
    {a b c : UIBHBOTPresentVertex W} (h : a = b) (p : Quiver.Path a c) :
    uibhbotPathEdges (h ▸ p) = uibhbotPathEdges p := by
  cases h
  rfl

/-- finite present path is itself a present edge of the code. -/
private theorem future_pathEdgeList_edgePresent
    {w : ℕ → Fin 3} {a b : PresentVertex w} (p : Quiver.Path a b) :
    ∀ f ∈ pathEdgeList p, EdgePresent w f := by
  induction p with
  | nil =>
      intro f hf
      simp only [pathEdgeList, List.not_mem_nil] at hf
  | cons p e ih =>
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact ih f hf
      · have he : f = e.val := List.mem_singleton.mp hf
        subst f
        exact e.property.1

/-- of a ray is lifted by `ae_uibhbotFuture_boundary_path_lift`; its last edge therefore has an
edge ID in the future copy, with the same global edge ID. -/
theorem ae_uibhbotFuture_infiniteRay_edges_in_future :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses
          (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ j : ℤ, j ≤ 0 →
            ∀ v : ℕ → UIBHBOTPresentVertex W,
              v 0 = (uibhbotFutureToGlobal k W).obj
                ⟨boundaryVertex
                  (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ →
              ∀ a : ∀ n : ℕ, v n ⟶ v (n + 1),
                ∀ n : ℕ, ∃ f : ℕ,
                  EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f ∧
                  uibhbotFutureEdge k W f = (a n).val := by
  filter_upwards [ae_uibhbotFuture_boundary_path_lift] with W hW k h j hj v hv a n
  let rayPrefix : ∀ m, Quiver.Path (v 0) (v m) := fun m =>
    Nat.rec Quiver.Path.nil (fun q p => p.cons (a q)) m
  have hlast : (a n).val ∈ uibhbotPathEdges (rayPrefix (n + 1)) := by
    change (a n).val ∈ uibhbotPathEdges ((rayPrefix n).cons (a n))
    simp only [uibhbotPathEdges]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨c, q, hc, hq, _⟩ := hW k h j hj (v (n + 1))
    (hv ▸ rayPrefix (n + 1))
  have hmem : (a n).val ∈ (pathEdgeList q).map (uibhbotFutureEdge k W) := by
    rw [← hq, future_pathEdges_cast_start hv]
    exact hlast
  rw [List.mem_map] at hmem
  obtain ⟨f, hf, hfe⟩ := hmem
  exact ⟨f, future_pathEdgeList_edgePresent q f hf, hfe⟩

/-- lift is unique because the future edge embedding is injective. Thus any choices made by lifts
of longer prefixes agree on their common edge IDs and form one infinite present path. -/
private theorem futureRay_lift_of_edge_lifts
    (k : ℤ) (W : ℤ → Fin 3)
    {s : PresentVertex (fun i => uibhbotFutureCode k W (i + 1))}
    (v : ℕ → UIBHBOTPresentVertex W)
    (hstart : v 0 = (uibhbotFutureToGlobal k W).obj s)
    (a : ∀ n : ℕ, v n ⟶ v (n + 1))
    (hlift : ∀ n : ℕ, ∃ f : ℕ,
      EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f ∧
        uibhbotFutureEdge k W f = (a n).val) :
    ∃ u : ℕ → PresentVertex (fun i => uibhbotFutureCode k W (i + 1)),
      ∃ e : ∀ n, u n ⟶ u (n + 1),
        u 0 = s ∧
        (∀ n, (uibhbotFutureToGlobal k W).obj (u n) = v n) ∧
        (∀ n, ((uibhbotFutureToGlobal k W).map (e n)).val = (a n).val) ∧
        (∀ n f, uibhbotFutureEdge k W f = (a n).val → f = (e n).val) := by
  classical
  let f : ℕ → ℕ := fun n => Classical.choose (hlift n)
  have hf (n : ℕ) :
      EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) (f n) ∧
        uibhbotFutureEdge k W (f n) = (a n).val := Classical.choose_spec (hlift n)
  let u : ℕ → PresentVertex (fun i => uibhbotFutureCode k W (i + 1)) :=
    fun n => ⟨edgeWest (fun i => uibhbotFutureCode k W (i + 1)) (f n)⟩
  have hwest (n : ℕ) : uibhbotFutureVertex k W
      (edgeWest (fun i => uibhbotFutureCode k W (i + 1)) (f n)) = (v n).id := by
    calc
      uibhbotFutureVertex k W
          (edgeWest (fun i => uibhbotFutureCode k W (i + 1)) (f n)) =
          wholePlaneEdgeWest W (uibhbotFutureEdge k W (f n)) :=
        (uibhbotFutureEdge_west k W (f n)).symm
      _ = wholePlaneEdgeWest W ((a n).val) := congrArg (wholePlaneEdgeWest W) (hf n).2
      _ = (v n).id := (a n).property.2.1
  have heast (n : ℕ) : uibhbotFutureVertex k W
      (edgeEast (fun i => uibhbotFutureCode k W (i + 1)) (f n)) = (v (n + 1)).id := by
    calc
      uibhbotFutureVertex k W
          (edgeEast (fun i => uibhbotFutureCode k W (i + 1)) (f n)) =
          wholePlaneEdgeEast W (uibhbotFutureEdge k W (f n)) :=
        (uibhbotFutureEdge_east k W (f n)).symm
      _ = wholePlaneEdgeEast W ((a n).val) := congrArg (wholePlaneEdgeEast W) (hf n).2
      _ = (v (n + 1)).id := (a n).property.2.2
  have hends (n : ℕ) :
      edgeEast (fun i => uibhbotFutureCode k W (i + 1)) (f n) =
        edgeWest (fun i => uibhbotFutureCode k W (i + 1)) (f (n + 1)) :=
    uibhbotFutureVertex_injective k W (heast n |>.trans (hwest (n + 1)).symm)
  let e : ∀ n, u n ⟶ u (n + 1) := fun n => ⟨f n, (hf n).1, rfl, hends n⟩
  have hobj (n : ℕ) : (uibhbotFutureToGlobal k W).obj (u n) = v n := by
    apply congrArg UIBHBOTPresentVertex.mk
    change uibhbotFutureVertex k W
        (edgeWest (fun i => uibhbotFutureCode k W (i + 1)) (f n)) = (v n).id
    exact hwest n
  have hmap (n : ℕ) :
      ((uibhbotFutureToGlobal k W).map (e n)).val = (a n).val := by
    change uibhbotFutureEdge k W (f n) = (a n).val
    exact (hf n).2
  have hu0 : u 0 = s := by
    apply uibhbotFutureToGlobal_obj_injective k W
    calc
      (uibhbotFutureToGlobal k W).obj (u 0) = v 0 := hobj 0
      _ = (uibhbotFutureToGlobal k W).obj s := hstart
  refine ⟨u, e, hu0, hobj, hmap, ?_⟩
  intro n g hge
  exact uibhbotFutureEdge_injective k W (hge.trans (hmap n).symm)

/-- the future-copy boundary vertex with relative index `j ≤ 0` lifts to an infinite present path
of that copy. Its image has the same vertices and edge IDs as the ray. -/
theorem ae_uibhbotFuture_infiniteRay_lift :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses
          (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ j : ℤ, j ≤ 0 →
            ∀ v : ℕ → UIBHBOTPresentVertex W,
              v 0 = (uibhbotFutureToGlobal k W).obj
                ⟨boundaryVertex
                  (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ →
              ∀ a : ∀ n : ℕ, v n ⟶ v (n + 1),
                ∃ u : ℕ → PresentVertex
                    (fun i => uibhbotFutureCode k W (i + 1)),
                  ∃ e : ∀ n, u n ⟶ u (n + 1),
                    u 0 = ⟨boundaryVertex
                      (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ ∧
                    (∀ n, (uibhbotFutureToGlobal k W).obj (u n) = v n) ∧
                    (∀ n, ((uibhbotFutureToGlobal k W).map (e n)).val = (a n).val) ∧
                    (∀ n f, uibhbotFutureEdge k W f = (a n).val → f = (e n).val) := by
  filter_upwards [ae_uibhbotFuture_infiniteRay_edges_in_future] with W hW k h j hj v hv a
  exact futureRay_lift_of_edge_lifts k W _ hv a (hW k h j hj v hv a)

/-- future-copy boundary index `j = l - k` is exactly the source label `xᵇᶜ_l`, since
`ae_uibhbotFutureBoundary_index` identifies its global vertex with
`uibhbotFutureVertex l W 0`. Every ray from that source label has all its edges in the future
copy. -/
theorem ae_uibhbotFuture_infiniteRay_edges_from_source_index :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ l : ℤ, l ≤ k →
          ∀ v : ℕ → UIBHBOTPresentVertex W,
            v 0 = ⟨uibhbotFutureVertex l W 0⟩ →
            ∀ a : ∀ n : ℕ, v n ⟶ v (n + 1),
              ∀ n : ℕ, ∃ f : ℕ,
                EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f ∧
                uibhbotFutureEdge k W f = (a n).val := by
  classical
  filter_upwards [ae_uibhbotFuture_infiniteRay_edges_in_future,
    ae_uibhbotFutureBoundary_index, ae_uibhbotFuture_boundaryHitWitnesses]
      with W hEdges hIndex hWitnesses k l hl v hv a n
  let h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)) :=
    hWitnesses k
  let j := l - k
  have hj : j ≤ 0 := by dsimp [j]; omega
  have hAlign := hIndex k h j hj
  have hSource : (uibhbotFutureToGlobal k W).obj
      ⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ =
        (⟨uibhbotFutureVertex l W 0⟩ : UIBHBOTPresentVertex W) := by
    apply congrArg UIBHBOTPresentVertex.mk
    change uibhbotFutureVertex k W
        (boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j) =
      uibhbotFutureVertex l W 0
    simpa only [show k + j = l by dsimp [j]; omega] using hAlign
  have hv' : v 0 = (uibhbotFutureToGlobal k W).obj
      ⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h j⟩ :=
    hv.trans hSource.symm
  exact hEdges k h j hj v hv' a n

/-- from the source boundary label `xᵇᶜ_l`, `l ≤ k`, uses the relative future-copy index `l-k`.
The lifted edge IDs are unique, so lifts of all finite ray prefixes are compatible. -/
theorem ae_uibhbotFuture_infiniteRay_lift_from_source_index :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ l : ℤ, l ≤ k →
          ∀ v : ℕ → UIBHBOTPresentVertex W,
            v 0 = ⟨uibhbotFutureVertex l W 0⟩ →
            ∀ a : ∀ n : ℕ, v n ⟶ v (n + 1),
              ∃ h : BoundaryHitWitnesses
                  (fun i => uibhbotFutureCode k W (i + 1)),
                ∃ u : ℕ → PresentVertex
                    (fun i => uibhbotFutureCode k W (i + 1)),
                  ∃ e : ∀ n, u n ⟶ u (n + 1),
                    u 0 = ⟨boundaryVertex
                      (fun i => uibhbotFutureCode k W (i + 1)) h (l - k)⟩ ∧
                    (∀ n, (uibhbotFutureToGlobal k W).obj (u n) = v n) ∧
                    (∀ n, ((uibhbotFutureToGlobal k W).map (e n)).val = (a n).val) ∧
                    (∀ n f, uibhbotFutureEdge k W f = (a n).val → f = (e n).val) := by
  classical
  filter_upwards [ae_uibhbotFuture_infiniteRay_edges_from_source_index,
    ae_uibhbotFutureBoundary_index, ae_uibhbotFuture_boundaryHitWitnesses]
      with W hEdges hIndex hWitnesses k l hl v hv a
  let h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)) :=
    hWitnesses k
  have hAlign := hIndex k h (l - k) (by omega)
  have hSource : (uibhbotFutureToGlobal k W).obj
      ⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h (l - k)⟩ =
        (⟨uibhbotFutureVertex l W 0⟩ : UIBHBOTPresentVertex W) := by
    apply congrArg UIBHBOTPresentVertex.mk
    change uibhbotFutureVertex k W
        (boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h (l - k)) =
      uibhbotFutureVertex l W 0
    simpa only [show k + (l - k) = l by omega] using hAlign
  have hv' : v 0 = (uibhbotFutureToGlobal k W).obj
      ⟨boundaryVertex (fun i => uibhbotFutureCode k W (i + 1)) h (l - k)⟩ :=
    hv.trans hSource.symm
  obtain ⟨u, e, hu0, hobj, hmap, hunique⟩ :=
    futureRay_lift_of_edge_lifts k W _ hv' a (hEdges k l hl v hv a)
  exact ⟨h, u, e, hu0, hobj, hmap, hunique⟩

end DirectedDistances.RandomWalk
