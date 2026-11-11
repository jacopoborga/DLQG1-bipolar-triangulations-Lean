/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SideAlignment2

/-! Helpers toward Lemma 5.6. This file aligns the Lemma 5.5 selected geodesics
with every slice witness at a fixed index. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: the selected left-side reader geodesic at an
index satisfies the source cut-leftmost predicate with its recorded path. -/
theorem m0LeftSideReaderWitness_cutLeftmost
    {W : ℤ → Fin 3} {x : XDP}
    (w : M0LeftSideReaderWitness W (if x = XDP.ldp then true else false))
    (j : ℤ) :
    Xdp.CutLeftmostXdp W w.H w.h w.hp w.hLL
      (if x = XDP.ldp then true else false) j (w.P j) (w.T j) :=
  w.hleft j

/-- Helper toward Lemma 5.6: the selected right-side reader geodesic at an
index satisfies the source cut-leftmost predicate with its recorded path. -/
theorem m0RightSideObservableWitness_cutLeftmost
    {W : ℤ → Fin 3} {x : XDP}
    (w : M0RightSideObservableWitness W (if x = XDP.ldp then true else false))
    (j : ℤ) :
    Xdp.CutLeftmostXdp W w.H w.h w.hp w.hLL
      (if x = XDP.ldp then true else false) j (w.P j) (w.T j) :=
  w.hleft j

/-- Helper toward Lemma 5.6: after matching the ambient data, two cut
geodesics with equal code paths are equal as source geodesics. -/
private theorem m0CutGeodesic_eq_of_codePath_eq
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (k : ℤ) (longest : Bool)
    (P Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (hcode : P.codePath = Q.codePath) : P = Q := by
  cases hP : P with
  | mk p hsegments hstart hstep =>
    cases hQ : Q with
    | mk q hsegments' hstart' hstep' =>
      have hpq : p = q := by simpa [hP, hQ] using hcode
      cases hpq
      rfl

/-- Helper toward Lemma 5.6: the left-reader code path agrees with every
slice witness code path at the same index, even when their reference paths
are different. -/
theorem m0LeftSideReaderWitness_codePath_eq_slice
    {W : ℤ → Fin 3} {x : XDP}
    (w : M0LeftSideReaderWitness W (if x = XDP.ldp then true else false))
    (s : M0CutGeodesicSliceWitness W x) (j : ℤ) :
    (w.P j).codePath = (s.P j).codePath := by
  have hH : w.H = s.H := Subsingleton.elim _ _
  have hh : w.h = s.h := Subsingleton.elim _ _
  have hLL : w.hLL = s.hLL := Subsingleton.elim _ _
  have hp : w.hp = s.hp := Subsingleton.elim _ _
  cases hH
  cases hh
  cases hLL
  cases hp
  exact m0CutGeodesicSlice_codePath_eq_of_cutLeftmost W s.H s.h s.hp s.hLL
    (if x = XDP.ldp then true else false) j (w.P j) (s.P j)
    (w.T j) (s.T j) (w.hleft j) (s.hleft j)

/-- Helper toward Lemma 5.6: the right-reader code path agrees with every
slice witness code path at the same index, even when their reference paths
are different. -/
theorem m0RightSideObservableWitness_codePath_eq_slice
    {W : ℤ → Fin 3} {x : XDP}
    (w : M0RightSideObservableWitness W (if x = XDP.ldp then true else false))
    (s : M0CutGeodesicSliceWitness W x) (j : ℤ) :
    (w.P j).codePath = (s.P j).codePath := by
  have hH : w.H = s.H := Subsingleton.elim _ _
  have hh : w.h = s.h := Subsingleton.elim _ _
  have hLL : w.hLL = s.hLL := Subsingleton.elim _ _
  have hp : w.hp = s.hp := Subsingleton.elim _ _
  cases hH
  cases hh
  cases hLL
  cases hp
  exact m0CutGeodesicSlice_codePath_eq_of_cutLeftmost W s.H s.h s.hp s.hLL
    (if x = XDP.ldp then true else false) j (w.P j) (s.P j)
    (w.T j) (s.T j) (w.hleft j) (s.hleft j)

/-- Helper toward Lemma 5.6: the left-reader side class equals the
corresponding side class of every slice witness at the same index. -/
theorem m0LeftSideReaderWitness_sideClass_eq_slice
    {W : ℤ → Fin 3} {x : XDP}
    (w : M0LeftSideReaderWitness W (if x = XDP.ldp then true else false))
    (s : M0CutGeodesicSliceWitness W x) (j : ℤ) (side : ThinMapSide) :
    geometricSideClass (m0GeodesicSide w.hp (w.P j) side) =
      geometricSideClass (m0GeodesicSide s.hp (s.P j) side) := by
  have hH : w.H = s.H := Subsingleton.elim _ _
  have hh : w.h = s.h := Subsingleton.elim _ _
  have hLL : w.hLL = s.hLL := Subsingleton.elim _ _
  have hp : w.hp = s.hp := Subsingleton.elim _ _
  cases hH
  cases hh
  cases hLL
  cases hp
  have hcode := m0LeftSideReaderWitness_codePath_eq_slice w s j
  have hP : w.P j = s.P j :=
    m0CutGeodesic_eq_of_codePath_eq W s.H s.h s.hLL j
      (if x = XDP.ldp then true else false) (w.P j) (s.P j) hcode
  rw [hP]

/-- Helper toward Lemma 5.6: the right-reader side class equals the
corresponding side class of every slice witness at the same index. -/
theorem m0RightSideObservableWitness_sideClass_eq_slice
    {W : ℤ → Fin 3} {x : XDP}
    (w : M0RightSideObservableWitness W (if x = XDP.ldp then true else false))
    (s : M0CutGeodesicSliceWitness W x) (j : ℤ) (side : ThinMapSide) :
    geometricSideClass (m0GeodesicSide w.hp (w.P j) side) =
      geometricSideClass (m0GeodesicSide s.hp (s.P j) side) := by
  have hH : w.H = s.H := Subsingleton.elim _ _
  have hh : w.h = s.h := Subsingleton.elim _ _
  have hLL : w.hLL = s.hLL := Subsingleton.elim _ _
  have hp : w.hp = s.hp := Subsingleton.elim _ _
  cases hH
  cases hh
  cases hLL
  cases hp
  have hcode := m0RightSideObservableWitness_codePath_eq_slice w s j
  have hP : w.P j = s.P j :=
    m0CutGeodesic_eq_of_codePath_eq W s.H s.h s.hLL j
      (if x = XDP.ldp then true else false) (w.P j) (s.P j) hcode
  rw [hP]

/-- Helper toward Lemma 5.6: almost surely, the left Option-valued Lemma 5.5
observable is the class of every slice witness side at a fixed index. -/
theorem ae_lemma55LeftSideClassOption_eq_sliceSideClass
    (x : XDP) (j : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        lemma55LeftSideClassOption x j W =
          some (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) := by
  filter_upwards [ae_m0LeftSideReaderWitness,
    ae_m0CutGeodesicSliceWitness x] with W hleft hs
  intro s
  let w : M0LeftSideReaderWitness W
      (if x = XDP.ldp then true else false) := Classical.choice (hleft _)
  have hoption := lemma55LeftSideClassOption_eq_some_of_nonempty x j W (hleft _)
  have hoption' : lemma55LeftSideClassOption x j W =
      some (geometricSideClass (m0GeodesicSide w.hp (w.P j) .left)) := by
    simpa [w] using hoption
  rw [hoption']
  exact congrArg some (m0LeftSideReaderWitness_sideClass_eq_slice w s j .left)

/-- Helper toward Lemma 5.6: almost surely, the right Option-valued Lemma 5.5
observable is the class of every slice witness side at a fixed index. -/
theorem ae_lemma55RightSideClassOption2_eq_sliceSideClass
    (x : XDP) (j : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        lemma55RightSideClassOption2 x j W =
          some (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) := by
  filter_upwards [ae_m0RightSideObservableWitness,
    ae_m0CutGeodesicSliceWitness x] with W hright hs
  intro s
  let w : M0RightSideObservableWitness W
      (if x = XDP.ldp then true else false) := Classical.choice (hright _)
  have hoption := lemma55RightSideClassOption2_eq_some_of_nonempty x j W (hright _)
  have hoption' : lemma55RightSideClassOption2 x j W =
      some (geometricSideClass (m0GeodesicSide w.hp (w.P j) .right)) := by
    simpa [w] using hoption
  rw [hoption']
  exact congrArg some (m0RightSideObservableWitness_sideClass_eq_slice w s j .right)

/-- Helper toward Lemma 5.6: on one probability-one event, the left
Option-valued observable agrees with every slice witness at every index. -/
theorem ae_all_lemma55LeftSideClassOption_eq_sliceSideClass (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ,
      ∀ s : M0CutGeodesicSliceWitness W x,
        lemma55LeftSideClassOption x j W =
          some (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) := by
  apply ae_all_iff.mpr
  intro j
  exact ae_lemma55LeftSideClassOption_eq_sliceSideClass x j

/-- Helper toward Lemma 5.6: on one probability-one event, the right
Option-valued observable agrees with every slice witness at every index. -/
theorem ae_all_lemma55RightSideClassOption2_eq_sliceSideClass (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ,
      ∀ s : M0CutGeodesicSliceWitness W x,
        lemma55RightSideClassOption2 x j W =
          some (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) := by
  apply ae_all_iff.mpr
  intro j
  exact ae_lemma55RightSideClassOption2_eq_sliceSideClass x j

/-- Helper toward Lemma 5.6: the left Option reader's defaulted value agrees
almost surely with every selected slice left-side class. -/
theorem ae_lemma55LeftSideClassOption_getD_eq_sliceSideClass
    (x : XDP) (j : ℤ) (default : GeometricSideClass) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        (lemma55LeftSideClassOption x j W).getD default =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .left) := by
  filter_upwards [ae_lemma55LeftSideClassOption_eq_sliceSideClass x j] with W hW
  intro s
  simpa using congrArg (fun o : Option GeometricSideClass => o.getD default) (hW s)

/-- Helper toward Lemma 5.6: the right Option reader's defaulted value agrees
almost surely with every selected slice right-side class. -/
theorem ae_lemma55RightSideClassOption2_getD_eq_sliceSideClass
    (x : XDP) (j : ℤ) (default : GeometricSideClass) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ s : M0CutGeodesicSliceWitness W x,
        (lemma55RightSideClassOption2 x j W).getD default =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right) := by
  filter_upwards [ae_lemma55RightSideClassOption2_eq_sliceSideClass x j] with W hW
  intro s
  simpa using congrArg (fun o : Option GeometricSideClass => o.getD default) (hW s)

/-- Helper toward Lemma 5.6: on one probability-one event, the left
defaulted observable agrees with every slice witness at every index. -/
theorem ae_all_lemma55LeftSideClassOption_getD_eq_sliceSideClass
    (x : XDP) (default : GeometricSideClass) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ,
      ∀ s : M0CutGeodesicSliceWitness W x,
        (lemma55LeftSideClassOption x j W).getD default =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .left) := by
  apply ae_all_iff.mpr
  intro j
  exact ae_lemma55LeftSideClassOption_getD_eq_sliceSideClass x j default

/-- Helper toward Lemma 5.6: on one probability-one event, the right
defaulted observable agrees with every slice witness at every index. -/
theorem ae_all_lemma55RightSideClassOption2_getD_eq_sliceSideClass
    (x : XDP) (default : GeometricSideClass) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ j : ℤ,
      ∀ s : M0CutGeodesicSliceWitness W x,
        (lemma55RightSideClassOption2 x j W).getD default =
          geometricSideClass (m0GeodesicSide s.hp (s.P j) .right) := by
  apply ae_all_iff.mpr
  intro j
  exact ae_lemma55RightSideClassOption2_getD_eq_sliceSideClass x j default































































end DirectedDistances.PaperProofs.Section5
