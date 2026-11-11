module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56Assembly2
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ForgetMarks

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6. Measurable mark forgetting preserves mutual
independence of an Option-valued family after applying the fixed-default class
reader. -/
theorem iIndepFun_forgetMarksOptionClassValue {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {G : ℤ → Ω → Option GeometricSideClass}
    (default : GeometricSideClass) (hG : iIndepFun G μ) :
    iIndepFun (fun k => forgetMarksOptionClassValue default ∘ G k) μ := by
  exact hG.comp (fun _ => forgetMarksOptionClassValue default)
    (fun _ => measurable_forgetMarksOptionClassValue default)

/-- Helper toward Lemma 5.6. Equality of laws for measurable Option-valued
observables passes through the fixed-default unmarked class map. -/
theorem map_forgetMarksOptionClassValue_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (default : GeometricSideClass)
    {f g : Ω → Option GeometricSideClass}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : μ.map f = μ.map g) :
    μ.map (forgetMarksOptionClassValue default ∘ f) =
      μ.map (forgetMarksOptionClassValue default ∘ g) := by
  calc
    μ.map (forgetMarksOptionClassValue default ∘ f) =
        (μ.map f).map (forgetMarksOptionClassValue default) :=
      (measurable_forgetMarksOptionClassValue default).aemeasurable
        (μ := μ.map f) |>.map_map_of_aemeasurable hf |>.symm
    _ = (μ.map g).map (forgetMarksOptionClassValue default) :=
      congrArg (fun ν : Measure (Option GeometricSideClass) =>
        ν.map (forgetMarksOptionClassValue default)) h
    _ = μ.map (forgetMarksOptionClassValue default ∘ g) :=
      (measurable_forgetMarksOptionClassValue default).aemeasurable
        (μ := μ.map g) |>.map_map_of_aemeasurable hg

/-- Helper toward Lemma 5.6. Package the independence and two half-index laws
of `lemma56_of_presentationDetermination` after forgetting the internal marks,
with exactly that theorem's hypotheses. -/
theorem lemma56_unmarked_of_presentationDetermination
    (default : GeometricSideClass)
    (x : XDP) (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : ∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure)
    (hPast : ∀ j, ∃ f : LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // k ≤ j}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56LeftCutObservation x j W))
    (hFuture : ∀ j, ∃ f : RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56RightCutObservation x j W))
    (F_L : LPlusThinPresentation → Option GeometricSideClass)
    (hFL : ∀ k, k ≤ 0 → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_L (geoSlice56LeftCutObservation x k W))
    (F_R : RMinusThinPresentation → Option GeometricSideClass)
    (hFR : ∀ k, 1 ≤ k → G k =ᵐ[wholePlaneIIDCodeMeasure]
      fun W => F_R (geoSlice56RightCutObservation x (k - 1) W)) :
    iIndepFun (fun k => forgetMarksOptionClassValue default ∘ G k)
        wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map (forgetMarksOptionClassValue default ∘ G 1)) ∧
      (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map (forgetMarksOptionClassValue default ∘ G 0)) := by
  have hmarked := lemma56_of_presentationDetermination x G hG hPast hFuture
    F_L hFL F_R hFR
  rcases hmarked with ⟨hind, hpositive, hnonpositive⟩
  refine ⟨iIndepFun_forgetMarksOptionClassValue default hind, ?_, ?_⟩
  · intro k hk
    exact map_forgetMarksOptionClassValue_eq default (hG k) (hG 1)
      (hpositive k hk)
  · intro k hk
    exact map_forgetMarksOptionClassValue_eq default (hG k) (hG 0)
      (hnonpositive k hk)

end DirectedDistances.PaperProofs.Section5
