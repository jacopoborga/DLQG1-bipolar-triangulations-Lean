module

public import DirectedDistances.PaperProofs.Section5.GeoSliceForgetMarksFamily
public import DirectedDistances.PaperProofs.Section5.GeoSliceRightReaders

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6. Iterate a previous-side update along a fixed
integer-indexed family. -/
theorem geoSlicePreviousSide_iterate {α : Type*} (prev : α → α)
    (side : ℤ → α) (hprev : ∀ j, prev (side j) = side (j - 1))
    (n : ℕ) (j : ℤ) :
    prev^[n] (side j) = side (j - n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, hprev j, ih (j - 1)]
      congr 1
      omega

/-- Helper toward Lemma 5.6. Iterate a next-side update along a fixed
integer-indexed family. -/
theorem geoSliceNextSide_iterate {α : Type*} (next : α → α)
    (side : ℤ → α) (hnext : ∀ j, next (side j) = side (j + 1))
    (n : ℕ) (j : ℤ) :
    next^[n] (side j) = side (j + n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, hnext j, ih (j + 1)]
      congr 1
      omega

/-- Helper toward Lemma 5.6. This reduction is conditional on the displayed
measurability, source-side update, and cut-observation reader hypotheses.
It turns those strictly weaker inputs into the past/future presentation
determination premises, then applies the mark-forgetting reduction. -/
theorem lemma56_unmarked_of_sliceReaders
    (default : GeometricSideClass) (x : XDP)
    (G : ℤ → (ℤ → Fin 3) → Option GeometricSideClass)
    (hG : ∀ k, AEMeasurable (G k) wholePlaneIIDCodeMeasure)
    (oneL : GeometricSideClass → Option GeometricSideClass)
    (prevL : GeometricSideClass → GeometricSideClass)
    (hL : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ j : ℤ,
        oneL (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) = G j W ∧
        prevL (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (j - 1)) .left))
    (oneR : GeometricSideClass → Option GeometricSideClass)
    (nextR : GeometricSideClass → GeometricSideClass)
    (hR : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ j : ℤ,
        oneR (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) =
          G (j + 1) W ∧
        nextR (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (j + 1)) .right))
    (readL : LPlusThinPresentation → GeometricSideClass)
    (hObsL : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ,
      ∀ s : M0CutGeodesicSliceWitness W x,
        readL (geoSlice56LeftCutObservation x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .left))
    (readR : RMinusThinPresentation → GeometricSideClass)
    (hObsR : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ,
      ∀ s : M0CutGeodesicSliceWitness W x,
        readR (geoSlice56RightCutObservation x j W) =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) :
    iIndepFun (fun k => forgetMarksOptionClassValue default ∘ G k)
        wholePlaneIIDCodeMeasure ∧
      (∀ k : ℤ, 1 ≤ k → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map (forgetMarksOptionClassValue default ∘ G 1)) ∧
      (∀ k : ℤ, k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (forgetMarksOptionClassValue default ∘ G k) =
        wholePlaneIIDCodeMeasure.map (forgetMarksOptionClassValue default ∘ G 0)) := by
  let F_L : LPlusThinPresentation → Option GeometricSideClass := fun c => oneL (readL c)
  let F_R : RMinusThinPresentation → Option GeometricSideClass := fun c => oneR (readR c)
  have hPast : ∀ j, ∃ f : LPlusThinPresentation →
      (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // k ≤ j}) => G k.val W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56LeftCutObservation x j W) := by
    intro j
    let f : LPlusThinPresentation →
        (∀ _k : {k : ℤ // k ≤ j}, Option GeometricSideClass) := fun c k =>
      oneL (prevL^[(j - k.val).toNat] (readL c))
    refine ⟨f, ?_⟩
    filter_upwards [hL, hObsL] with W hL hObs
    obtain ⟨s, hs⟩ := hL
    funext k
    change G k.val W = oneL
      (prevL^[(j - k.val).toNat] (readL (geoSlice56LeftCutObservation x j W)))
    have hrec : ∀ n, prevL
        (geometricSideClass (m0GeodesicSide s.hp (s.P n) .left)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (n - 1)) .left) :=
      fun n => (hs n).2
    have hn : ((j - k.val).toNat : ℤ) = j - k.val :=
      Int.toNat_of_nonneg (sub_nonneg.mpr k.property)
    have hidx : j - ((j - k.val).toNat : ℤ) = k.val := by rw [hn]; omega
    rw [← (hs k.val).1, hObs j s, geoSlicePreviousSide_iterate prevL
      (fun n => geometricSideClass (m0GeodesicSide s.hp (s.P n) .left))
      hrec (j - k.val).toNat j]
    rw [hidx]
  have hFuture : ∀ j, ∃ f : RMinusThinPresentation →
      (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass),
      (fun W (k : {k : ℤ // j + 1 ≤ k}) => G k.val W) =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => f (geoSlice56RightCutObservation x j W) := by
    intro j
    let f : RMinusThinPresentation →
        (∀ _k : {k : ℤ // j + 1 ≤ k}, Option GeometricSideClass) := fun c k =>
      oneR (nextR^[(k.val - (j + 1)).toNat] (readR c))
    refine ⟨f, ?_⟩
    filter_upwards [hR, hObsR] with W hR hObs
    obtain ⟨s, hs⟩ := hR
    funext k
    change G k.val W = oneR
      (nextR^[(k.val - (j + 1)).toNat]
        (readR (geoSlice56RightCutObservation x j W)))
    have hrec : ∀ n, nextR
        (geometricSideClass (m0GeodesicSide s.hp (s.P n) .right)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (n + 1)) .right) :=
      fun n => (hs n).2
    have hn : ((k.val - (j + 1)).toNat : ℤ) = k.val - (j + 1) :=
      Int.toNat_of_nonneg (sub_nonneg.mpr k.property)
    have hidx : j + ((k.val - (j + 1)).toNat : ℤ) = k.val - 1 := by
      rw [hn]
      omega
    have hone : oneR
        (geometricSideClass (m0GeodesicSide s.hp (s.P (k.val - 1)) .right)) =
          G k.val W := by
      simpa only [sub_add_cancel] using (hs (k.val - 1)).1
    rw [← hone, hObs j s, geoSliceNextSide_iterate nextR
      (fun n => geometricSideClass (m0GeodesicSide s.hp (s.P n) .right))
      hrec (k.val - (j + 1)).toNat j]
    rw [hidx]
  exact lemma56_unmarked_of_presentationDetermination default x G hG hPast hFuture
    F_L (by
      intro k hk
      filter_upwards [hL, hObsL] with W hL hObs
      obtain ⟨s, hs⟩ := hL
      change G k W = oneL (readL (geoSlice56LeftCutObservation x k W))
      rw [← (hs k).1, hObs k s])
    F_R (by
      intro k hk
      filter_upwards [hR, hObsR] with W hR hObs
      obtain ⟨s, hs⟩ := hR
      change G k W = oneR (readR (geoSlice56RightCutObservation x (k - 1) W))
      have hone : oneR
          (geometricSideClass (m0GeodesicSide s.hp (s.P (k - 1)) .right)) = G k W := by
        simpa only [sub_add_cancel] using (hs (k - 1)).1
      rw [← hone, hObs (k - 1) s])
































































end DirectedDistances.PaperProofs.Section5
