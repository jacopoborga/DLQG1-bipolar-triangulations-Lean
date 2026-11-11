module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmap
public import DirectedDistances.KMSW.BoundaryLabelling

/-! Geometric edge range for the future copy in Lemma 5.10
records exactly the present future-code edges. The full geometric range also
contains the future code's missing boundary edges. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section5

/-- absolute active edge suffix is exactly the image of future-code edges which
are present in the directed carrier. -/
theorem uibhbotFutureEdge_present_range_eq_suffix (k : ℤ) (W : ℤ → Fin 3) :
    (uibhbotFutureEdge k W) '' {f | EdgePresent
      (fun i => uibhbotFutureCode k W (i + 1)) f} =
        {e | ∃ t : ℤ, uibhbotBoundaryHitTime k W ≤ t ∧
          uibhbotAbsoluteActiveEdge W t = e} :=
  uibhbotFuture_presentEdge_image k W

/-- future-code edge missing from the directed carrier cannot be an absolute
active edge at or after the boundary hit. -/
theorem uibhbotFutureEdge_missing_not_suffix (k : ℤ) (W : ℤ → Fin 3)
    {f : ℕ} (hf : ¬ EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f) :
    uibhbotFutureEdge k W f ∉ {e | ∃ t : ℤ,
      uibhbotBoundaryHitTime k W ≤ t ∧ uibhbotAbsoluteActiveEdge W t = e} := by
  intro hsuffix
  have hpresent : uibhbotFutureEdge k W f ∈
      (uibhbotFutureEdge k W) '' {g | EdgePresent
        (fun i => uibhbotFutureCode k W (i + 1)) g} := by
    simpa only [uibhbotFutureEdge_present_range_eq_suffix] using hsuffix
  obtain ⟨g, hg, hgf⟩ := hpresent
  have hindex : g = f := uibhbotFutureEdge_injective k W hgf
  subst g
  exact hf hg

/-- future code has a missing lower-left boundary edge at relative index `-1`,
almost surely. -/
theorem ae_uibhbotFutureCode_has_missingEdge :
    ∀ᵐ W ∂(DirectedDistances.PaperProofs.Section5.uibhbotCodeLawRel :
      Measure (ℤ → Fin 3)),
      ∀ k : ℤ, ∃ f,
        ¬ EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f := by
  refine ae_uibhbotFuture_boundaryHitWitnesses.mono ?_
  intro W hW k
  refine ⟨boundaryOuterEdge (fun i => uibhbotFutureCode k W (i + 1)) (hW k) (-1), ?_⟩
  exact (boundaryOuterEdge_endpoints
    (fun i => uibhbotFutureCode k W (i + 1)) (hW k) (-1)).2.2.2 (by omega)

/-- unrestricted geometric range is almost surely strictly larger than the suffix
of absolute active edges, because it retains the missing lower-left boundary
edge. -/
theorem ae_uibhbotFutureEdge_range_ne_suffix :
    ∀ᵐ W ∂(DirectedDistances.PaperProofs.Section5.uibhbotCodeLawRel :
      Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        Set.range (uibhbotFutureEdge k W) ≠
          {e | ∃ t : ℤ, uibhbotBoundaryHitTime k W ≤ t ∧
            uibhbotAbsoluteActiveEdge W t = e} := by
  refine ae_uibhbotFutureCode_has_missingEdge.mono ?_
  intro W hW k
  obtain ⟨f, hf⟩ := hW k
  have hmissing := uibhbotFutureEdge_missing_not_suffix k W hf
  intro heq
  apply hmissing
  have hrange : uibhbotFutureEdge k W f ∈ Set.range (uibhbotFutureEdge k W) :=
    ⟨f, rfl⟩
  rw [heq] at hrange
  exact hrange

/-- full geometric range decomposes into the suffix of absolute active edges and
the images of future-code edges missing from its directed carrier. -/
theorem uibhbotFutureEdge_range_eq_suffix_union_missing (k : ℤ)
    (W : ℤ → Fin 3) :
    Set.range (uibhbotFutureEdge k W) =
      {e | ∃ t : ℤ, uibhbotBoundaryHitTime k W ≤ t ∧
        uibhbotAbsoluteActiveEdge W t = e} ∪
        (uibhbotFutureEdge k W) '' {f | ¬ EdgePresent
          (fun i => uibhbotFutureCode k W (i + 1)) f} := by
  ext e
  constructor
  · rintro ⟨f, rfl⟩
    by_cases hf : EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f
    · left
      have hmem : uibhbotFutureEdge k W f ∈ (uibhbotFutureEdge k W) ''
          {g | EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) g} :=
        ⟨f, hf, rfl⟩
      simpa only [uibhbotFutureEdge_present_range_eq_suffix k W] using hmem
    · right
      exact ⟨f, hf, rfl⟩
  · intro he
    rcases he with hsuffix | ⟨f, hf, hfe⟩
    · have hpresent : e ∈ (uibhbotFutureEdge k W) '' {f |
          EdgePresent (fun i => uibhbotFutureCode k W (i + 1)) f} := by
        simpa only [uibhbotFutureEdge_present_range_eq_suffix k W] using hsuffix
      obtain ⟨f, hf, hfe⟩ := hpresent
      exact ⟨f, hfe⟩
    · exact ⟨f, hfe⟩

end DirectedDistances.RandomWalk
