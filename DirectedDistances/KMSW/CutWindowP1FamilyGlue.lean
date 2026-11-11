module

public import DirectedDistances.KMSW.BusemannM0FromP1
public import DirectedDistances.KMSW.InftyCutP1Compose
public import DirectedDistances.KMSW.WindowModelHatCodes
public import DirectedDistances.KMSW.HatImageLimit

/-! Supporting lemmas for paper labels `lem-infty-cut`, `lem-quad-kmsw`, `thm-busemann` (see CORRESPONDENCE.md). -/

/-! # Conditional assembly from the deterministic hatted simulation

This module reduces the iid-code boundary Busemann conclusions associated
remaining OPEN deterministic premise `HatInputExists`. It composes the
with the shifted embedding for `lem-infty-cut` (127–143).
This is a conditional reduction and is NOT `thm-busemann`. -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory DirectedDistances.RandomWalk






@[expose] def HatInputExists : Prop :=
  ∀ (w : ℕ → Fin 3) (h : HasFlowLineHits w),
    ∃ eφ vφ : ℕ → ℕ,
      HatImageLimitInput (hatCodes w h) w (quadrantRStageTime w h) eφ vφ

private theorem pathEdgeList_edgePresent {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) :
    ∀ e ∈ pathEdgeList p, EdgePresent w e := by
  induction p with
  | nil =>
    intro e he
    simp only [pathEdgeList, List.not_mem_nil] at he
  | cons p f ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ih e he
    · have hef : e = f.val := List.mem_singleton.mp he
      subst e
      exact f.property.1





theorem cutWindowP1Family_of_hatInput (hH : HatInputExists) :
    ∀ᵐ ω ∂iidCodeMeasure, CutWindowP1Family ω := by
  classical
  filter_upwards [iidCodes_ae_cutWindow_model_hatCodes] with ω hω
  intro h
  have hK : ∀ K : ℕ,
      ∃ f : PresentVertex (cutWindowRPhaseCodes ω h K) ↪
          PresentVertex (fun i => ω (i + 1)),
        (∀ z : PresentVertex (fun i => ω (i + 1)),
          (∃ r : Path
            (⟨boundaryVertex (fun i => ω (i + 1)) h (-(K : ℤ))⟩ :
              PresentVertex (fun i => ω (i + 1))) z,
            ∀ e ∈ pathEdgeList r,
              ∀ he : EdgePresent (fun i => ω (i + 1)) e,
                boundaryHitTime (fun i => ω (i + 1)) h (-(K : ℤ)) ≤
                  actTime (fun i => ω (i + 1)) e he) →
          ∃ b : PresentVertex (cutWindowRPhaseCodes ω h K),
            f b = z ∧
              ∃ N, b.id < (kmswStage (cutWindowRPhaseCodes ω h K) N).nextVertex) ∧
        (∀ i : ℕ,
          i ∈ cutWindowP3AllocatedIds (cutWindowRPhaseCodes ω h K)
            (fun i => ω (i + 1)) f h K →
          ∀ {v} (q : Path
            (f (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K))) v),
            (∀ e ∈ pathEdgeList q,
              e ∈ cutWindowP3Region (fun i => ω (i + 1)) h K) →
            ∃ b : PresentVertex (cutWindowRPhaseCodes ω h K),
              ∃ r : Path (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) b,
                f b = v ∧ ∀ y ∈ r.vertices, f y ∈ q.vertices) := by
    intro K
    let w : ℕ → Fin 3 := fun i => ω (i + 1)
    let τ := boundaryHitTime w h (-(K : ℤ))
    let u := cutWindowRPhaseCodes ω h K
    obtain ⟨hτ, hmodel⟩ := hω h K
    obtain ⟨eφ, vφ, hD⟩ := hH (fun i => ω (τ + i + 1)) hτ
    have D : HatImageLimitInput u (fun i => w (τ + i))
        (quadrantRStageTime (fun i => ω (τ + i + 1)) hτ) eφ vφ := by
      change HatImageLimitInput (cutWindowRPhaseCodes ω h K)
        (fun i => ω (τ + i + 1)) _ eφ vφ
      rw [hmodel]
      exact hD
    obtain ⟨f₀, hInjective, hRoot, hLift, hRange, _hReach⟩ := hatImageLimit D
    have H1inj : ∀ {a b}, kmswVertexAllocated u a → kmswVertexAllocated u b →
        f₀ a = f₀ b → a = b := by
      intro a b ha hb hab
      exact hInjective a b ha hb hab
    have H1alloc : ∀ a, kmswVertexAllocated u a →
        kmswVertexAllocated (fun i => w (τ + i)) (f₀ a) := by
      intro a _
      exact kmswVertexAllocated_all _ _
    have H2 : ∀ a, kmswVertexAllocated u a →
        ∀ {v} (q : Path (f₀ a) v),
          ∃ b : PresentVertex u, kmswVertexAllocated u b ∧
            ∃ r : Path a b, f₀ b = v ∧ ∀ y ∈ r.vertices, f₀ y ∈ q.vertices := by
      intro a ha v q
      exact hLift a ha v q
    have H3 : ∀ {v : PresentVertex (fun i => w (τ + i))},
        Path (⟨0⟩ : PresentVertex (fun i => w (τ + i))) v →
          ∃ b : PresentVertex u, kmswVertexAllocated u b ∧ f₀ b = v := by
      intro v q
      exact hRange v ⟨q⟩
    let f := shiftComposeEmbedding u w τ f₀ H1inj H1alloc
    obtain ⟨hP1, hLateRange, _hBoundaryRoot⟩ := cutWindow_shiftCompose ω h K
      f₀ H1inj H1alloc H2 H3 hRoot (cutWindowP3AllocatedIds u w f h K)
    refine ⟨f, ?_, ?_⟩
    · intro z hz
      obtain ⟨r, hr⟩ := hz
      have hLate : ∀ e ∈ pathEdgeList r, e ∈ cutLateRegion w τ := by
        intro e he
        exact (mem_cutLateRegion_iff w τ e
          (pathEdgeList_edgePresent r e he)).2 (hr e he)
      obtain ⟨b, hb, hfb⟩ := hLateRange r hLate
      exact ⟨b, hfb, hb⟩
    · intro i hi v q hq
      apply hP1 i hi q
      intro e he
      exact (mem_cutLateRegion_iff w τ e
        (pathEdgeList_edgePresent q e he)).2 (hq e he)
  let f := fun K => Classical.choose (hK K)
  refine ⟨f, ?_, ?_⟩
  · intro K
    exact (Classical.choose_spec (hK K)).1
  · intro K
    exact (Classical.choose_spec (hK K)).2




theorem iidCodes_ae_boundaryBusemannSDP_of_hatInput
    (hH : HatInputExists) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannSDP
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) ∧
          (∀ l k : ℤ, 0 ≤ l → l < k →
            X l - X k ≤
              ((sdp (boundaryPresentVertex (fun i => ω (i + 1)) h l)
                (boundaryPresentVertex (fun i => ω (i + 1)) h k)).toNat : ℤ)) ∧
          (∀ k : ℤ, 1 ≤ k → -1 ≤ X k - X (k - 1)) := by
  exact iidCodes_ae_boundaryBusemannSDP_of_P1 (cutWindowP1Family_of_hatInput hH)




theorem iidCodes_ae_boundaryBusemannLDP_of_hatInput
    (hH : HatInputExists) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannLDP
              (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) ∧
          (∀ l k : ℤ, 0 ≤ l → l < k →
            ∀ hr : Reachable
              (boundaryPresentVertex (fun i => ω (i + 1)) h l)
              (boundaryPresentVertex (fun i => ω (i + 1)) h k),
              (presentLdpFiniteNat
                (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin) hr : ℤ) ≤
                X l - X k) ∧
          (∀ k : ℤ, 1 ≤ k → X k - X (k - 1) ≤ -1) := by
  exact iidCodes_ae_boundaryBusemannLDP_of_P1 (cutWindowP1Family_of_hatInput hH)

end DirectedDistances.KMSW
