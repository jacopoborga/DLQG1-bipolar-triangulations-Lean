module

public import DirectedDistances.PaperProofs.Section7.CellSDPUpperFirstBullet
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperSeparatorTargets
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.RandomWalk.IIDCodeStrongMarkov
import DirectedDistances.KMSW.RawGeodesicAE

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Filter MeasureTheory Quiver DirectedDistances.KMSW DirectedDistances.RandomWalk
  DirectedDistances.Recursive

private theorem shifted_code_tail_eq (ω : ℕ → Fin 3) (n : ℕ) :
    (fun i => (codeShift n ω) (i + 1)) = fun i => ω (n + i + 1) := by
  funext i
  simp only [codeShift, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_assoc]

private theorem iidCodes_ae_shifted_busemannSDPMeasurableVersion :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ n : ℕ,
      ∃ hn : BoundaryHitWitnesses (fun i => ω (n + i + 1)),
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => ω (n + i + 1)) hn)
          (busemannSDPMeasurableVersion (codeShift n ω)) := by
  rw [ae_all_iff]
  intro n
  have hmap : ∀ᵐ η ∂iidCodeMeasure.map (codeShift n),
      ∃ h : BoundaryHitWitnesses (fun i => η (i + 1)),
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => η (i + 1)) h)
          (busemannSDPMeasurableVersion η) := by
    simpa only [map_codeShift] using
      (iidCodes_ae_busemannSDPMeasurableVersion :
        ∀ᵐ η ∂iidCodeMeasure,
          ∃ h : BoundaryHitWitnesses (fun i => η (i + 1)),
            IsBoundaryBusemannSDP
              (boundaryPresentVertex (fun i => η (i + 1)) h)
              (busemannSDPMeasurableVersion η))
  have hshift := (Measure.tendsto_ae_map
    (measurable_codeShift n).aemeasurable).eventually hmap
  filter_upwards [hshift] with ω hω
  rw [shifted_code_tail_eq ω n] at hω
  exact hω




theorem cellSdpUpper_first_bullet_ae :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ n : ℕ, ∀ h0 : BoundaryHitWitnesses w,
        ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)),
          ∀ M0 Mn : ℤ,
            (∀ ℓ : ℤ,
              -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
              ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
              |busemannSDPMeasurableVersion ω ℓ -
                busemannSDPMeasurableVersion ω
                  ((kmswStage w n).LR.length : ℤ)| ≤ M0) →
            (∀ k : ℤ,
              -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k →
              k ≤ ((kmswStage w n).UR.length : ℤ) + 1 →
              |busemannSDPMeasurableVersion (codeShift n ω) k -
                busemannSDPMeasurableVersion (codeShift n ω)
                  (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)| ≤ Mn) →
            ∀ ℓ : ℤ,
              -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
              ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
              boundaryVertex w h0 ℓ < (kmswStage w n).nextVertex →
              ∃ (hTargets : ∀ k : ℤ,
                ∃ y : ℕ → PresentVertex (fun i => w (n + i)),
                  Function.Injective y ∧
                  (∀ j, Reachable
                    (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
                    Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
                      (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
                  (∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
                    (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w))),
                (∀ k : ℤ, ∃ J : ℕ, ∀ j, J ≤ j →
                  (sdp (boundaryPresentVertex (fun i => w (n + i)) hn k)
                    ((Classical.choose (hTargets k)) j)).toNat ≤
                  (sdp
                    (⟨kmswWindowVertexMapInf w n
                      (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w)
                    (⟨kmswWindowVertexMapInf w n
                      ((Classical.choose (hTargets k)) j).id⟩ : PresentVertex w)).toNat) →
                ∃ k : ℤ,
                  -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
                  k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
                  sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
                    ⟨kmswWindowVertexMapInf w n
                      (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
                    (((2 * M0 + 2 * Mn).toNat : ℕ) : ℕ∞) := by
  filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion,
    iidCodes_ae_shifted_busemannSDPMeasurableVersion,
    iidCodes_ae_boundary_infinite_extremal, cell_sdp_separator_targets] with
    ω hbase hshift hgeo hseparator
  dsimp only at hseparator
  intro w n h0 hn M0 Mn hM0 hMn ℓ hℓL hℓR hℓStage
  obtain ⟨hbaseWitness, hbaseX⟩ := hbase
  have hX : IsBoundaryBusemannSDP (boundaryPresentVertex _ h0)
      (busemannSDPMeasurableVersion ω) := by
    simpa using hbaseX
  obtain ⟨hnWitness, hshiftX⟩ := hshift n
  have hXn : IsBoundaryBusemannSDP
      (boundaryPresentVertex (fun i => w (n + i)) hn)
      (busemannSDPMeasurableVersion (codeShift n ω)) := by
    simpa [w] using hshiftX
  obtain ⟨P, hP⟩ := (hgeo h0 ℓ).2
  let hTargets := hseparator n h0 hn ℓ
  refine ⟨hTargets, ?_⟩
  intro hconf
  exact cellSdpUpper_first_bullet_of_targets w n h0 hn
    (busemannSDPMeasurableVersion ω)
    (busemannSDPMeasurableVersion (codeShift n ω)) M0 Mn hX hXn hM0 hMn
    ℓ ⟨hℓL, hℓR⟩ hℓStage P hP hTargets hconf

end DirectedDistances.PaperProofs.Section7
