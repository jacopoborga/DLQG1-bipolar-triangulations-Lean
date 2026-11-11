module

public import DirectedDistances.KMSW.MonotoneSeamRegions

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Classical

noncomputable section

variable (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)





@[expose] noncomputable def seamCuts (k : ℤ) : Finset ℝ :=
  (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
    (futureMapBoundaryDart w h k)).points.map Complex.re).toFinset





private theorem seam_point_mem_image (p : Polyline) {z : ℂ} (hz : z ∈ p.points) :
    z ∈ p.image := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
  have hlt : i.val < p.points.length := i.isLt
  have heq : p.point i.val = z := by
    change p.points.getD i.val p.start = z
    rw [List.getD_eq_getElem _ _ hlt]
    exact hi
  rw [← heq]
  by_cases hzero : i.val = 0
  · have hp : p.point i.val = p.start := by
      rw [hzero, p.point_zero_eq_start]
    rw [hp]
    exact Or.inl rfl
  · have hindex : (i.val - 1) + 1 = i.val := by omega
    refine Or.inr ⟨i.val - 1, by omega, ?_⟩
    change p.point i.val ∈ segment ℝ (p.point (i.val - 1))
      (p.point ((i.val - 1) + 1))
    rw [hindex]
    exact right_mem_segment ℝ _ _





theorem seamX_mem_seamCuts (k : ℤ) :
    seamX w h hfin k ∈ seamCuts w h hfin k := by
  classical
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let d := futureMapBoundaryDart w h k
  have hd : kmswLimitDartVertex w d = boundaryVertex w h (k + 1) :=
    (futureMapBoundaryDart_endpoints w h k).1
  have hf : kmswLimitDartVertex w (futureMapEdgeInv d) = boundaryVertex w h k :=
    (futureMapBoundaryDart_endpoints w h k).2
  have hs : (P.arc d).start = P.pos (boundaryVertex w h (k + 1)) := by
    calc
      (P.arc d).start = P.pos (kmswLimitDartVertex w d) := P.arc_start d
      _ = P.pos (boundaryVertex w h (k + 1)) := congrArg P.pos hd
  have he : (P.arc d).finish = P.pos (boundaryVertex w h k) := by
    calc
      (P.arc d).finish = P.pos (kmswLimitDartVertex w (futureMapEdgeInv d)) := by
        simpa [P, d, futureMapBoundaryDart, futureMapEdgeInv] using P.arc_finish d
      _ = P.pos (boundaryVertex w h k) := congrArg P.pos hf
  unfold seamCuts
  simp only [List.mem_toFinset, List.mem_map]
  refine ⟨(P.arc d).finish, List.getLast_mem (P.arc d).nonempty, ?_⟩
  simp [seamX, P, he]





theorem seamX_succ_mem_seamCuts (k : ℤ) :
    seamX w h hfin (k + 1) ∈ seamCuts w h hfin k := by
  classical
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let d := futureMapBoundaryDart w h k
  have hd : kmswLimitDartVertex w d = boundaryVertex w h (k + 1) :=
    (futureMapBoundaryDart_endpoints w h k).1
  have hs : (P.arc d).start = P.pos (boundaryVertex w h (k + 1)) := by
    calc
      (P.arc d).start = P.pos (kmswLimitDartVertex w d) := P.arc_start d
      _ = P.pos (boundaryVertex w h (k + 1)) := congrArg P.pos hd
  unfold seamCuts
  simp only [List.mem_toFinset, List.mem_map]
  refine ⟨(P.arc d).start, List.head_mem (P.arc d).nonempty, ?_⟩
  simp [seamX, P, hs]





theorem seamCuts_subset_Icc (k : ℤ) :
    (seamCuts w h hfin k : Set ℝ) ⊆
      Icc (seamX w h hfin k) (seamX w h hfin (k + 1)) := by
  intro x hx
  classical
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let p := P.arc (futureMapBoundaryDart w h k)
  have hx' : x ∈ (p.points.map Complex.re).toFinset := by
    simpa [seamCuts, P, p] using hx
  have hmap : x ∈ p.points.map Complex.re := List.mem_toFinset.mp hx'
  obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hmap
  have hzimg : z ∈ p.image := seam_point_mem_image p hz
  have hstrip := (seam_arc_vertical_sections w h hfin k).1 z hzimg
  rw [← hzx]
  exact hstrip





@[expose] noncomputable def seamCutSet : Set ℝ :=
  ⋃ k : ℤ, (seamCuts w h hfin k : Set ℝ)





theorem seamCutSet_inter_Icc_finite (s t : ℝ) :
    (seamCutSet w h hfin ∩ Icc s t).Finite := by
  classical
  obtain ⟨ks, hksl, hksr⟩ := seamX_tiling w h hfin s
  obtain ⟨kt, hktl, hktr⟩ := seamX_tiling w h hfin t
  let K : Set ℤ := Icc (ks - 1) (kt + 1)
  have hK : K.Finite := by
    change (Icc (ks - 1) (kt + 1) : Set ℤ).Finite
    exact Set.finite_Icc _ _
  have hB : (⋃ k ∈ K, (seamCuts w h hfin k : Set ℝ)).Finite := by
    apply hK.biUnion
    intro k hk
    exact (seamCuts w h hfin k).finite_toSet
  apply hB.subset
  intro x hx
  rcases hx with ⟨hxcut, hxst⟩
  rcases Set.mem_iUnion.mp hxcut with ⟨k, hkcut⟩
  have hkc := seamCuts_subset_Icc w h hfin k hkcut
  have hlow : seamX w h hfin ks ≤ seamX w h hfin (k + 1) := by
    exact le_trans hksl (le_trans hxst.1 hkc.2)
  have hhigh : seamX w h hfin k ≤ seamX w h hfin (kt + 1) := by
    exact le_trans hkc.1 (le_trans hxst.2 hktr)
  have hkl : ks ≤ k + 1 := (seamX_strictMono w h hfin).le_iff_le.mp hlow
  have hkr : k ≤ kt + 1 := (seamX_strictMono w h hfin).le_iff_le.mp hhigh
  have hkK : k ∈ K := by
    change ks - 1 ≤ k ∧ k ≤ kt + 1
    omega
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkK, hkcut⟩⟩

end
end DirectedDistances.KMSW
