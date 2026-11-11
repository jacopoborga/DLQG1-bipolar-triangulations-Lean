module

public import DirectedDistances.PaperProofs.Section5.GeoInftyIndFourTuple












public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4




@[expose] noncomputable def leftSideObsNonneg (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) :
    (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3) :=
  (boundaryFourObservations x k 0 W,
    boundaryFourObservations x k 1 W, boundaryFourObservations x k 3 W)




@[expose] noncomputable def rightSideObsNonneg (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) : ℕ → Option FiniteThinMap :=
  boundaryFourObservations x k 2 W




@[expose] noncomputable def leftSideObsNonpos (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) : (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) :=
  (boundaryFourObservations x k 3 W, boundaryFourObservations x k 1 W)




@[expose] noncomputable def rightSideObsNonpos (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) : (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) :=
  (boundaryFourObservations x k 0 W, boundaryFourObservations x k 2 W)




theorem leftSideObsNonneg_indep_rightSideObsNonneg (x : XDP) (k : ℤ) :
    IndepFun (leftSideObsNonneg x k) (rightSideObsNonneg x k)
      wholePlaneIIDCodeMeasure := by
  let S : Finset (Fin 4) := {0, 1, 3}
  let T : Finset (Fin 4) := {2}
  have h := iIndepFun.indepFun_finset₀ S T (by decide)
    (boundaryFourObservations_iIndepFun x k)
    (aemeasurable_boundaryFourObservations x k)
  exact h.comp
    (φ := fun (v : ∀ i : S, BoundaryFourObservation i) =>
      (v ⟨0, by decide⟩, v ⟨1, by decide⟩, v ⟨3, by decide⟩))
    (ψ := fun (v : ∀ i : T, BoundaryFourObservation i) => v ⟨2, by decide⟩)
    ((measurable_pi_apply (X := fun i : S => BoundaryFourObservation i)
      ⟨0, by decide⟩).prodMk
      ((measurable_pi_apply (X := fun i : S => BoundaryFourObservation i)
        ⟨1, by decide⟩).prodMk
        (measurable_pi_apply (X := fun i : S => BoundaryFourObservation i)
          ⟨3, by decide⟩)))
    (measurable_pi_apply (X := fun i : T => BoundaryFourObservation i)
      ⟨2, by decide⟩)




theorem leftSideObsNonpos_indep_rightSideObsNonpos (x : XDP) (k : ℤ) :
    IndepFun (leftSideObsNonpos x k) (rightSideObsNonpos x k)
      wholePlaneIIDCodeMeasure := by
  exact (boundaryFourObservations_iIndepFun x k).indepFun_prodMk_prodMk₀
    (aemeasurable_boundaryFourObservations x k) 3 1 0 2
    (by decide) (by decide) (by decide) (by decide)




theorem rightSideObsNonneg_law_eq_zero (x : XDP) (k : ℤ) (_hk : 0 ≤ k) :
    wholePlaneIIDCodeMeasure.map (rightSideObsNonneg x k) =
      wholePlaneIIDCodeMeasure.map (rightSideObsNonneg x 0) := by
  let F := fun j W =>
    ((boundaryFourObservations x j 1 W, boundaryFourObservations x j 2 W),
      boundaryFourObservations x j 3 W)
  let project : (BoundaryFourObservation 1 × BoundaryFourObservation 2) ×
      BoundaryFourObservation 3 → BoundaryFourObservation 2 := fun v => v.1.2
  have hproject : Measurable project := measurable_snd.comp measurable_fst
  have hF (j : ℤ) : AEMeasurable (F j) wholePlaneIIDCodeMeasure :=
    ((aemeasurable_boundaryFourObservations x j 1).prodMk
      (aemeasurable_boundaryFourObservations x j 2)).prodMk
      (aemeasurable_boundaryFourObservations x j 3)
  have hlaw : wholePlaneIIDCodeMeasure.map (F k) =
      wholePlaneIIDCodeMeasure.map (F 0) := boundaryFutureSideTriple_law_eq_zero x k
  change wholePlaneIIDCodeMeasure.map (project ∘ F k) =
    wholePlaneIIDCodeMeasure.map (project ∘ F 0)
  rw [← AEMeasurable.map_map_of_aemeasurable hproject.aemeasurable (hF k),
    ← AEMeasurable.map_map_of_aemeasurable hproject.aemeasurable (hF 0), hlaw]




theorem leftSideObsNonpos_law_eq_zero (x : XDP) (k : ℤ) (_hk : k ≤ 0) :
    wholePlaneIIDCodeMeasure.map (leftSideObsNonpos x k) =
      wholePlaneIIDCodeMeasure.map (leftSideObsNonpos x 0) := by
  let F := fun j W =>
    ((boundaryFourObservations x j 1 W, boundaryFourObservations x j 2 W),
      boundaryFourObservations x j 3 W)
  let project : (BoundaryFourObservation 1 × BoundaryFourObservation 2) ×
      BoundaryFourObservation 3 → BoundaryFourObservation 3 ×
        BoundaryFourObservation 1 := fun v => (v.2, v.1.1)
  have hproject : Measurable project :=
    measurable_snd.prodMk (measurable_fst.comp measurable_fst)
  have hF (j : ℤ) : AEMeasurable (F j) wholePlaneIIDCodeMeasure :=
    ((aemeasurable_boundaryFourObservations x j 1).prodMk
      (aemeasurable_boundaryFourObservations x j 2)).prodMk
      (aemeasurable_boundaryFourObservations x j 3)
  have hlaw : wholePlaneIIDCodeMeasure.map (F k) =
      wholePlaneIIDCodeMeasure.map (F 0) := boundaryFutureSideTriple_law_eq_zero x k
  change wholePlaneIIDCodeMeasure.map (project ∘ F k) =
    wholePlaneIIDCodeMeasure.map (project ∘ F 0)
  rw [← AEMeasurable.map_map_of_aemeasurable hproject.aemeasurable (hF k),
    ← AEMeasurable.map_map_of_aemeasurable hproject.aemeasurable (hF 0), hlaw]

end DirectedDistances.PaperProofs.Section5
