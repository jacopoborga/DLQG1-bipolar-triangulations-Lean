/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLeftReconstruction
public import DirectedDistances.PaperProofs.Section5.GeoSliceFaceChainClopen2
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SideAlignment2
public import DirectedDistances.PaperProofs.Section5.GeoSliceIntrinsicSliceReader3
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Final

/-! Left updates and explicitly conditional slice measurability reductions. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: both intrinsic left updates hold on one event
of full measure for the same slice witness and every integer index. -/
theorem m0Cut_ae_leftSideUpdates (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ j : ℤ,
        oneL (if x = XDP.ldp then true else false)
            (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) =
          m0CutGeodesicSliceClassOption x j W ∧
        prevL (if x = XDP.ldp then true else false)
            (geometricSideClass (m0GeodesicSide s.hp (s.P j) .left)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (j - 1)) .left) := by
  apply m0Cut_ae_leftSideUpdates_of_exhaustion x
  intro W H h hLL hp longest P T hleft k hcontain c hc hoff
  exact m0GeodesicLeftSide_off_ray_previousRight_reached
    hp P T hleft k hcontain c hc (by cases c <;> exact hoff)

/-- Helper toward Lemma 5.6: select the left side class of a source slice
witness, using the displayed default only when no witness exists. -/
@[expose] noncomputable def m0CutSliceLeftSideClass
    (default : GeometricSideClass) (x : XDP) (k : ℤ) (W : ℤ → Fin 3) :
    GeometricSideClass :=
  if h : Nonempty (M0CutGeodesicSliceWitness W x) then
    geometricSideClass (m0GeodesicSide (Classical.choice h).hp
      ((Classical.choice h).P k) .left)
  else default

/-- Helper toward Lemma 5.6: the selected left class agrees with every
slice witness; this uses the imported witness-independence theorem. -/
theorem m0CutSliceLeftSideClass_eq
    (default : GeometricSideClass) {x : XDP} {W : ℤ → Fin 3}
    (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    m0CutSliceLeftSideClass default x k W =
      geometricSideClass (m0GeodesicSide s.hp (s.P k) .left) := by
  rw [m0CutSliceLeftSideClass, dite_eq_left ⟨s⟩]
  exact m0CutGeodesicSliceWitness_sideClass_eq _ s k .left

/-- Helper toward Lemma 5.6: the optional slice class is almost surely
obtained by applying the intrinsic reader to the selected left class. -/
theorem m0CutGeodesicSliceClassOption_ae_eq_oneL
    (default : GeometricSideClass) (x : XDP) (k : ℤ) :
    m0CutGeodesicSliceClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      oneL (if x = XDP.ldp then true else false) ∘
        m0CutSliceLeftSideClass default x k := by
  filter_upwards [m0Cut_ae_leftSideUpdates x] with W hW
  obtain ⟨s, hs⟩ := hW
  change _ = oneL _ (m0CutSliceLeftSideClass default x k W)
  rw [m0CutSliceLeftSideClass_eq default s k]
  exact (hs k).1.symm

/-- Helper toward Lemma 5.6: conditional reduction of `hG` to exactly two
measurability inputs, for the left-side law and the selected left class. -/
theorem aemeasurable_m0CutGeodesicSliceClassOption_of_leftSide
    (default : GeometricSideClass) (x : XDP) (k : ℤ)
    (hOne : AEMeasurable (oneL (if x = XDP.ldp then true else false))
      (wholePlaneIIDCodeMeasure.map (m0CutSliceLeftSideClass default x k)))
    (hSide : AEMeasurable (m0CutSliceLeftSideClass default x k)
      wholePlaneIIDCodeMeasure) :
    AEMeasurable (m0CutGeodesicSliceClassOption x k) wholePlaneIIDCodeMeasure := by
  exact (hOne.comp_aemeasurable hSide).congr
    (m0CutGeodesicSliceClassOption_ae_eq_oneL default x k).symm

/-- Helper toward Lemma 5.6: the quotient sigma-algebra reduces reader
measurability exactly to measurability on numbered submaps. -/
theorem measurable_oneL_iff (longest : Bool) :
    Measurable (oneL longest) ↔ Measurable (leftOneSlice longest) := by
  exact Iff.rfl

/-- Helper toward Lemma 5.6: the Lemma 5.5 reader and a slice witness
select the same left side, even if their reference paths differ. -/
theorem m0CutGeodesicSliceWitness_leftReader_sideClass_eq
    {W : ℤ → Fin 3} {x : XDP}
    (s : M0CutGeodesicSliceWitness W x)
    (w : M0LeftSideReaderWitness W (if x = XDP.ldp then true else false))
    (k : ℤ) :
    geometricSideClass (m0GeodesicSide s.hp (s.P k) .left) =
      geometricSideClass (m0GeodesicSide w.hp (w.P k) .left) := by
  have hH : s.H = w.H := Subsingleton.elim _ _
  have hh : s.h = w.h := Subsingleton.elim _ _
  have hhp : s.hp = w.hp := Subsingleton.elim _ _
  have hLL : s.hLL = w.hLL := Subsingleton.elim _ _
  cases hH
  cases hh
  cases hLL
  cases hhp
  have hcode := m0CutGeodesicSlice_codePath_eq_of_cutLeftmost W s.H s.h s.hp s.hLL
    (if x = XDP.ldp then true else false) k (s.P k) (w.P k)
    (s.T k) (w.T k) (s.hleft k) (w.hleft k)
  have hP : s.P k = w.P k := by
    cases hleft : s.P k with
    | mk P hsegments hstart hstep =>
      cases hright : w.P k with
      | mk Q hsegments' hstart' hstep' =>
        have hpath : P = Q := by
          simpa only [hleft, hright] using hcode
        cases hpath
        rfl
  rw [hP]

/-- Helper toward Lemma 5.6: the optional Lemma 5.5 observable equals the
left class of every slice witness whenever that witness exists. -/
theorem lemma55LeftSideClassOption_eq_of_sliceWitness
    {W : ℤ → Fin 3} {x : XDP}
    (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    lemma55LeftSideClassOption x k W =
      some (geometricSideClass (m0GeodesicSide s.hp (s.P k) .left)) := by
  let w : M0LeftSideReaderWitness W (if x = XDP.ldp then true else false) :=
    ⟨s.H, s.h, s.hLL, s.hp, s.T, s.P, s.hleft, s.huniq⟩
  rw [lemma55LeftSideClassOption_eq_some_of_nonempty x k W ⟨w⟩]
  exact congrArg some
    (m0CutGeodesicSliceWitness_leftReader_sideClass_eq s (Classical.choice ⟨w⟩) k).symm

/-- Helper toward Lemma 5.6: Lemma 5.5 supplies a.e. measurability of the
optional left class at every integer index, including zero. -/
theorem aemeasurable_lemma55LeftSideClassOption_all (x : XDP) (k : ℤ) :
    AEMeasurable (lemma55LeftSideClassOption x k) wholePlaneIIDCodeMeasure := by
  by_cases hk : 0 < k
  · exact aemeasurable_lemma55LeftSideClassOption_pos x k hk
  · have hk' : k ≤ 0 := le_of_not_gt hk
    exact ((aemeasurable_LMinusSidePresentation_classOption4 x k hk').comp_aemeasurable
      (aemeasurable_decodeLMinus_leftSideObsNonpos x k)).congr
        (lemma55LeftSideClassOption_ae_eq_LMinusSidePresentation_classOption4 x k hk').symm

/-- Helper toward Lemma 5.6: the selected slice-witness left class is
almost surely the class-valued Lemma 5.5 observable with the same default. -/
theorem m0CutSliceLeftSideClass_ae_eq_lemma55
    (default : GeometricSideClass) (x : XDP) (k : ℤ) :
    m0CutSliceLeftSideClass default x k =ᵐ[wholePlaneIIDCodeMeasure]
      lemma55OptionClassValue default ∘ lemma55LeftSideClassOption x k := by
  filter_upwards [ae_m0CutGeodesicSliceWitness x,
    (lemma55_marked_sides default x k).1] with W hW hval
  let s := Classical.choice hW
  change m0CutSliceLeftSideClass default x k W =
    lemma55OptionClassValue default (lemma55LeftSideClassOption x k W)
  rw [m0CutSliceLeftSideClass_eq default s k]
  exact Option.some.inj ((lemma55LeftSideClassOption_eq_of_sliceWitness s k).symm.trans hval)

/-- Helper toward Lemma 5.6: the left class of a selected slice witness
is a.e. measurable, with no alignment or measurability premise. -/
theorem aemeasurable_m0CutSliceLeftSideClass
    (default : GeometricSideClass) (x : XDP) (k : ℤ) :
    AEMeasurable (m0CutSliceLeftSideClass default x k) wholePlaneIIDCodeMeasure := by
  exact ((measurable_lemma55OptionClassValue default).comp_aemeasurable
    (aemeasurable_lemma55LeftSideClassOption_all x k)).congr
      (m0CutSliceLeftSideClass_ae_eq_lemma55 default x k).symm

/-- Helper toward Lemma 5.6: conditional reduction with only the displayed
reader measurability input; the source left class is already a.e. measurable. -/
theorem aemeasurable_m0CutGeodesicSliceClassOption_of_oneL
    (default : GeometricSideClass) (x : XDP) (k : ℤ)
    (hOne : AEMeasurable (oneL (if x = XDP.ldp then true else false))
      (wholePlaneIIDCodeMeasure.map (m0CutSliceLeftSideClass default x k))) :
    AEMeasurable (m0CutGeodesicSliceClassOption x k) wholePlaneIIDCodeMeasure := by
  exact aemeasurable_m0CutGeodesicSliceClassOption_of_leftSide default x k hOne
    (aemeasurable_m0CutSliceLeftSideClass default x k)

/-- Helper toward Lemma 5.6: on every source slice witness, the intrinsic
right candidate in its left side is exactly the preceding right side.
The off-ray exhaustion is proved, rather than a hypothesis. -/
theorem M0CutGeodesicSliceWitness.left_intrinsic_right_iff_previousRight
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ)
    (c : GeometricSideCell (m0GeodesicSide s.hp (s.P k) .left)) :
    geometricSide_intrinsic_right (m0GeodesicSide s.hp (s.P k) .left)
        (m0GeodesicSideAdjacentVertices s.hp s.P k (s.left_adjacent_containment k))
        (m0GeodesicSideAdjacentDarts s.hp s.P k (s.left_adjacent_containment k)) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices s.hp (s.P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges s.hp (s.P (k - 1)) .right := by
  have hA := m0GeodesicLeftSide_intrinsic_right_iff_previousRight_of_exhaustion
    s.hp s.P k (s.left_adjacent_containment k) (by
      intro c hc hoff
      exact m0GeodesicLeftSide_off_ray_previousRight_reached
        s.hp s.P s.T s.hleft k (s.left_adjacent_containment k) c hc
          (by cases c <;> exact hoff))
  cases c <;> exact hA _

/-- Helper toward Lemma 5.6: the source slice realizes the complete
intrinsic left restriction without an exhaustion premise. -/
theorem M0CutGeodesicSliceWitness.left_sliceRealizes
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    leftSliceRealizes (if x = XDP.ldp then true else false)
      (m0GeodesicSide s.hp (s.P k) .left)
      (m0CutGeodesicSlice (hp := s.hp) s.P k
        (s.thetaMinus k) (s.theta k) (s.least k)) := by
  exact m0GeodesicLeftSide_sliceRealizes_of_openA s.hp s.P s.T s.hleft k
    (s.left_adjacent_containment k)
    (fun c => by cases c <;> exact s.left_intrinsic_right_iff_previousRight k _)
    (s.thetaMinus k) (s.theta k) (s.least k)

/-- Helper toward Lemma 5.6: on a source side the intrinsic optional
reader returns precisely the actual slice class. -/
theorem M0CutGeodesicSliceWitness.leftOneSlice_eq
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    leftOneSlice (if x = XDP.ldp then true else false)
        (m0GeodesicSide s.hp (s.P k) .left) =
      some (geometricSideClass (m0CutGeodesicSlice (hp := s.hp) s.P k
        (s.thetaMinus k) (s.theta k) (s.least k))) :=
  leftOneSlice_eq_of_realizes (s.left_sliceRealizes k)

/-- Helper toward Lemma 5.6: the intrinsic left reader agrees on source
sides with the fixed measurable labeled-pair reader. This identity does
not assert measurability of the selected common-coordinate pair. -/
theorem M0CutGeodesicSliceWitness.leftOneSlice_eq_sidePairReader
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    leftOneSlice (if x = XDP.ldp then true else false)
        (m0GeodesicSide s.hp (s.P k) .left) =
      geoSliceSidePairClassOption (s.sidePairData k) := by
  exact (s.leftOneSlice_eq k).trans (s.sidePairData_class k).symm
























































/- declarations reported exactly [propext, Classical.choice, Quot.sound].
The probe compile exited 0. The probes were removed before the final -/

end DirectedDistances.PaperProofs.Section5
