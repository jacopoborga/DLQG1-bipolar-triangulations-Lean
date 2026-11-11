module

public import DirectedDistances.PaperProofs.Section5.M0GeodesicSideCarrier
public import DirectedDistances.PaperProofs.Section5.BoundaryFutureThinSides
public import DirectedDistances.PaperProofs.Section5.DirectedContainMapClause
public import DirectedDistances.PaperProofs.Section5.GeoInftyCutLeftmostXdp
public import DirectedDistances.KMSW.WholePlaneLemma38IntegerStart
public import DirectedDistances.KMSW.GluingBoundaryOrder
import DirectedDistances.KMSW.RawGeodesicTransport
import DirectedDistances.KMSW.UIQBOTOrientation
import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfLaunchSeed
import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfSeamArg
import DirectedDistances.KMSW.WholePlaneGlueFaceOrbits

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! The five geometric edge carriers below have run-zero IDs. In particular, the
prefix with its active edge removed is a set difference, even at time zero.
The future embedding acts on every geometric edge, including missing edges.
The hatted side carriers are the literal geometric sides of `sourceAncestorPath`
on the existing coherent-domain event. The route-54 path is identified edge by
edge with the embedded hatted path below. Identification of the glued closed
regions remains an obligation; it is not a premise of any theorem in this file. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open MeasureTheory

variable (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)



@[expose] noncomputable def boundaryGluingFutureStream : ℕ → Fin 3 :=
  fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)



@[expose] noncomputable def boundaryGluingEdgeMap : ℕ → ℕ :=
  kmswWindowEdgeMapInf (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)



theorem boundaryGluingEdgeMap_injective : Function.Injective (boundaryGluingEdgeMap W h k) :=
  kmswWindowEdgeMapInf_injective _ _

 
theorem boundaryGluingEdgeMap_wholePlane (e : ℕ) :
    wholePlaneEdgeι W 0 (boundaryGluingEdgeMap W h k e) =
      lemma38StartEdgeι W (boundaryHitTime (shiftedStream W 0) h k : ℤ) e := by
  let t := boundaryHitTime (shiftedStream W 0) h k
  change wholePlaneEdgeι W 0 (kmswWindowEdgeMapInf (shiftedStream W 0) t e) =
    lemma38StartEdgeι W (t : ℤ) e
  by_cases ht : t = 0
  · simp only [ht, lemma38StartEdgeι, Nat.cast_zero, le_refl, ↓reduceIte, Int.natAbs_zero,
      kmswWindowEdgeMapInf_zero_start]
    rfl
  · have ht' : ¬ (t : ℤ) ≤ 0 := by omega
    simp only [lemma38StartEdgeι, ht', ↓reduceIte, Int.toNat_natCast]



@[expose] noncomputable def boundaryGluingPrefixEdges : Set ℕ :=
  {e | e < (kmswStage (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)).nextEdge}



@[expose] noncomputable def boundaryGluingPrefixMinusEdges : Set ℕ :=
  boundaryGluingPrefixEdges W h k \
    {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)}



theorem boundaryGluing_active_mem_prefix :
    act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) ∈
      boundaryGluingPrefixEdges W h k :=
  act_lt_nextEdge _ le_rfl



theorem boundaryGluing_active_eq_boundaryOuterEdge (hk : 0 ≤ k) :
    act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) =
      boundaryOuterEdge (shiftedStream W 0) h k := by
  by_cases hk0 : k = 0
  · subst k
    rw [boundaryHitTime_zero, boundaryOuterEdge_zero]
    rfl
  · have hj : 1 ≤ k.toNat := by omega
    rw [boundaryOuterEdge_of_positive _ h (show 1 ≤ k by omega)]
    simpa only [Int.toNat_of_nonneg hk] using
      (boundaryHitTime_right_boundary_edge (shiftedStream W 0) h hj).1

 
theorem mem_boundaryGluingPrefixMinusEdges (e : ℕ) :
    e ∈ boundaryGluingPrefixMinusEdges W h k ↔
      e ∈ boundaryGluingPrefixEdges W h k ∧
        e ≠ act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) :=
  Iff.rfl

 
theorem boundaryGluingPrefixMinusEdges_subset :
    boundaryGluingPrefixMinusEdges W h k ⊆ boundaryGluingPrefixEdges W h k :=
  Set.sdiff_subset



theorem boundaryGluing_active_not_mem_prefixMinus :
    act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) ∉
      boundaryGluingPrefixMinusEdges W h k := by
  intro he
  exact he.2 rfl

 
theorem boundaryGluingPrefixEdges_finite : (boundaryGluingPrefixEdges W h k).Finite :=
  Set.finite_Iio _

 
theorem boundaryGluingPrefixMinusEdges_finite :
    (boundaryGluingPrefixMinusEdges W h k).Finite :=
  (boundaryGluingPrefixEdges_finite W h k).subset
    (boundaryGluingPrefixMinusEdges_subset W h k)



theorem boundaryGluingPrefixEdges_zero : boundaryGluingPrefixEdges W h 0 = {0} := by
  ext e
  simp only [boundaryGluingPrefixEdges, boundaryHitTime_zero, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  change e < 1 ↔ e = 0
  omega



theorem boundaryGluingPrefixMinusEdges_zero :
    boundaryGluingPrefixMinusEdges W h 0 = ∅ := by
  rw [boundaryGluingPrefixMinusEdges, boundaryGluingPrefixEdges_zero,
    boundaryHitTime_zero]
  change ({0} : Set ℕ) \ {0} = ∅
  exact Set.sdiff_self

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))



@[expose] noncomputable def boundaryGluingHatEdgeMap : ℕ → ℕ :=
  boundaryGluingEdgeMap W h k ∘ hatLimitEdgeMap (boundaryGluingFutureStream W h k) hτ



@[expose] noncomputable def boundaryGluingPrimedEdgeMap : ℕ → ℕ :=
  boundaryGluingEdgeMap W h k ∘ primedLimitEdgeMap (boundaryGluingFutureStream W h k) hτ



theorem boundaryGluingHatEdgeMap_injective :
    Function.Injective (boundaryGluingHatEdgeMap W h k hτ) :=
  (boundaryGluingEdgeMap_injective W h k).comp (hatLimitEdgeMap_injective _ hτ)



theorem boundaryGluingPrimedEdgeMap_injective :
    Function.Injective (boundaryGluingPrimedEdgeMap W h k hτ) :=
  (boundaryGluingEdgeMap_injective W h k).comp (primedLimitEdgeMap_injective _ hτ)



@[expose] noncomputable def boundaryGluingPrimedEdges : Set ℕ :=
  Set.range (boundaryGluingPrimedEdgeMap W h k hτ)



theorem boundaryGluing_decoded_stream :
    boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)) =
      hatCodes (boundaryGluingFutureStream W h k) hτ := by
  rw [boundaryFutureHattedPath, boundaryFuture_hatLawCodes_eq_hatCodes W h k hτ]
  funext i
  apply lazyTwoDimensionalStep_injective
  have hs : integrateCodes (hatCodes (boundaryGluingFutureStream W h k) hτ) (i + 1) -
      integrateCodes (hatCodes (boundaryGluingFutureStream W h k) hτ) i =
      lazyTwoDimensionalStep (hatCodes (boundaryGluingFutureStream W h k) hτ i) := by
    simp only [integrateCodes, Finset.sum_range_succ]
    abel
  exact (step_pathCode _ i ⟨_, hs.symm⟩).trans hs

variable (x : XDP)
  (hq : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)



@[expose] noncomputable def boundaryGluingHatSideEdges (s : ThinMapSide) : Set ℕ :=
  boundaryGluingHatEdgeMap W h k hτ ''
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s
      ⟨boundaryFutureHattedPath k W, hq⟩).edges



@[expose] noncomputable def boundaryGluingLeftHatEdges : Set ℕ :=
  boundaryGluingHatSideEdges W h k hτ x hq .left



@[expose] noncomputable def boundaryGluingRightHatEdges : Set ℕ :=
  boundaryGluingHatSideEdges W h k hτ x hq .right




@[expose] noncomputable def boundaryGluingHatSeamEdges : Set ℕ :=
  boundaryGluingHatEdgeMap W h k hτ '' Set.range
    (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hq⟩).edge



theorem boundaryGluingHatSeamEdges_subset_both :
    boundaryGluingHatSeamEdges W h k hτ x hq ⊆
      boundaryGluingLeftHatEdges W h k hτ x hq ∩
        boundaryGluingRightHatEdges W h k hτ x hq := by
  rintro e ⟨a, ⟨i, rfl⟩, rfl⟩
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  have hseam (s : ThinMapSide) :
      (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q).edge i ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s q).edges := by
    change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
      renewalTime_positiveSuccessTime s q j
    rw [iUnion_geometricAncestorEdges]
    exact seamEdge_mem_sideEdges _ _ _ _ _ _ s i
  exact ⟨⟨_, hseam .left, rfl⟩, ⟨_, hseam .right, rfl⟩⟩



private theorem gluing_arc_interior_nonempty {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (G : PLDrawing D V flip rot vert)
    (d : D) : (G.arc d).interior.Nonempty := by
  let p := G.arc d
  let a := midpoint ℝ p.start (p.point 1)
  let b := midpoint ℝ p.start a
  have hne : p.start ≠ p.point 1 := by
    intro he
    exact G.initial_nonzero d (sub_eq_zero.mpr he.symm)
  have ha : a ≠ p.start := fun he => hne ((midpoint_eq_left_iff ℝ).mp he)
  have hb : b ≠ p.start := by
    intro he
    exact ha ((midpoint_eq_left_iff ℝ).mp he).symm
  have hba : b ≠ a := by
    intro he
    exact ha ((midpoint_eq_right_iff ℝ).mp he).symm
  have ham : a ∈ segment ℝ p.start (p.point 1) := midpoint_mem_segment _ _
  have hbm : b ∈ segment ℝ p.start (p.point 1) :=
    (convex_segment p.start (p.point 1)).segment_subset
      (left_mem_segment ℝ p.start (p.point 1)) ham (midpoint_mem_segment p.start a)
  have himage {z : ℂ} (hz : z ∈ segment ℝ p.start (p.point 1)) : z ∈ p.image := by
    refine Or.inr ⟨0, ?_, ?_⟩
    · have hl := G.arc_length d
      change 2 ≤ p.points.length at hl
      omega
    · change z ∈ segment ℝ (p.point 0) (p.point 1)
      rw [Polyline.point_zero_eq_start]
      exact hz
  by_cases haf : a = p.finish
  · refine ⟨b, himage hbm, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hb, fun he => hba (he.trans haf.symm)⟩
  · refine ⟨a, himage ham, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha, haf⟩



private theorem gluing_sideEdges_inter (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (P : InfinitePresentPath w ⟨0⟩) :
    sideEdges w hfin hL htrans hR P .left ∩
      sideEdges w hfin hL htrans hR P .right = Set.range P.edge := by
  let G := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have htrace : thinMapSideRegion w hfin hL htrans hR P .left ∩
      thinMapSideRegion w hfin hL htrans hR P .right ⊆
        pathTrace G (fun i => (P.edge i, false)) := by
    rintro z ⟨⟨⟨r, hr, hre, hri⟩, _⟩, _, hup⟩
    have hzi : z.im = r.im := le_antisymm (hup r hr hre) hri
    exact (Complex.ext hre hzi.symm) ▸ hr
  apply Set.Subset.antisymm
  · rintro e ⟨hl, hr⟩
    classical
    by_contra he
    obtain ⟨z, hz⟩ := gluing_arc_interior_nonempty G (e, false)
    have hzP := htrace ⟨hl hz.1, hr hz.1⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzP
    have hne (b : Bool) : (P.edge i, false) ≠ (e, b) := by
      intro hh
      exact he ⟨i, congrArg Prod.fst hh⟩
    have hnotStart : z ≠ (G.arc (P.edge i, false)).start := by
      intro hh
      exact G.interior_avoids_vertices (e, false) _
        ((hh.trans (G.arc_start _)) ▸ hz)
    have hnotFinish : z ≠ (G.arc (P.edge i, false)).finish := by
      intro hh
      exact G.interior_avoids_vertices (e, false) _
        ((hh.trans (G.arc_finish _)) ▸ hz)
    have hiz : z ∈ (G.arc (P.edge i, false)).interior :=
      ⟨hi, by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
        And.intro hnotStart hnotFinish⟩
    exact Set.disjoint_left.mp
      (G.interior_disjoint (e, false) (P.edge i, false) (hne false) (hne true)) hz hiz
  · rintro e ⟨i, rfl⟩
    exact ⟨seamEdge_mem_sideEdges w hfin hL htrans hR P .left i,
      seamEdge_mem_sideEdges w hfin hL htrans hR P .right i⟩




theorem boundaryGluingLeftHatEdges_inter_rightHatEdges :
    boundaryGluingLeftHatEdges W h k hτ x hq ∩
      boundaryGluingRightHatEdges W h k hτ x hq =
        boundaryGluingHatSeamEdges W h k hτ x hq := by
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  change boundaryGluingHatEdgeMap W h k hτ ''
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges ∩
    boundaryGluingHatEdgeMap W h k hτ ''
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges = _
  rw [← Set.image_inter (boundaryGluingHatEdgeMap_injective W h k hτ)]
  change boundaryGluingHatEdgeMap W h k hτ ''
      ((⋃ s, geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime .left q s) ∩
        ⋃ s, geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime .right q s) = _
  rw [iUnion_geometricAncestorEdges, iUnion_geometricAncestorEdges, gluing_sideEdges_inter]
  rfl




@[expose] noncomputable def boundaryGluingBetaEdges : Set ℕ :=
  Set.range (fun i => boundaryGluingHatEdgeMap W h k hτ
    (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) i))



theorem boundaryGluingBetaEdges_subset_leftHatEdges :
    boundaryGluingBetaEdges W h k hτ ⊆ boundaryGluingLeftHatEdges W h k hτ x hq := by
  rintro e ⟨i, rfl⟩
  refine ⟨_, ?_, rfl⟩
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  change _ ∈ ⋃ s, geometricAncestorEdges x renewalTime
    renewalTime_positiveSuccessTime .left q s
  rw [iUnion_geometricAncestorEdges, ← boundaryGluing_decoded_stream W h k hτ]
  have ht := leftBoundaryTrace_subset_sideRegion
    (boltzmannKMSWStream (pathCode q.1))
    (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q)
  intro z hz
  exact ht (Set.mem_iUnion.mpr ⟨i, hz⟩)

variable (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))




theorem boundaryGluingBeta_edge_primed (i : ℕ) :
    boundaryGluingHatEdgeMap W h k hτ
        (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) i) =
      boundaryGluingPrimedEdgeMap W h k hτ
        (primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
          (hatBoundaryHitWitnesses _ hτ) hfin i) ∧
      ¬ PrimedEdgePresent (boundaryGluingFutureStream W h k) hτ
        (primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
          (hatBoundaryHitWitnesses _ hτ) hfin i) := by
  let u := boundaryGluingFutureStream W h k
  have hg := gluingBoundary_same_index u hτ hfin (hatBoundaryHitWitnesses u hτ)
    hfin i (primedIntervalBase (primedSimInput u) hτ i + 1) le_rfl
  exact ⟨congrArg (boundaryGluingEdgeMap W h k) hg.1, hg.2.2⟩



theorem boundaryGluingPrimedEdges_inter_hatRange
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    boundaryGluingPrimedEdges W h k hτ ∩ Set.range (boundaryGluingHatEdgeMap W h k hτ) =
      boundaryGluingBetaEdges W h k hτ := by
  let u := boundaryGluingFutureStream W h k
  let hb := hatBoundaryHitWitnesses u hτ
  apply Set.Subset.antisymm
  · rintro e ⟨⟨a, ha⟩, ⟨b, rfl⟩⟩
    have he : primedLimitEdgeMap u hτ a = hatLimitEdgeMap u hτ b :=
      boundaryGluingEdgeMap_injective W h k ha
    have hp : primeGeomEdge u hfin hb (hatLimitEdgeMap u hτ b) :=
      (primeGeomEdge_iff_primedLimitEdge u hfin hb hτ _).mpr ⟨a, he⟩
    have hh : MhatGeometricEdge u (hatLimitEdgeMap u hτ b) :=
      (hatLimitEdgeMap_geometric_range_iff u hτ _).mp ⟨b, rfl⟩
    have hbeta : primeBetaEdge u hfin hb (hatLimitEdgeMap u hτ b) := by
      rcases hp with hp | hp
      · exact (hp hh).elim
      · exact hp
    obtain ⟨i, hi⟩ := hbeta
    refine ⟨i, ?_⟩
    apply congrArg (boundaryGluingEdgeMap W h k)
    exact (hattedLeftBoundaryBeta0EdgeCorrespondence_proved u hτ hfin hb i).trans hi
  · rintro e ⟨i, rfl⟩
    exact ⟨⟨_, (boundaryGluingBeta_edge_primed W h k hτ hfin i).1.symm⟩, ⟨_, rfl⟩⟩



theorem boundaryGluingPrimedEdges_inter_leftHatEdges
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    boundaryGluingPrimedEdges W h k hτ ∩ boundaryGluingLeftHatEdges W h k hτ x hq =
      boundaryGluingBetaEdges W h k hτ := by
  apply Set.Subset.antisymm
  · rintro e ⟨hp, a, ha, he⟩
    rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin]
    exact ⟨hp, a, he⟩
  · intro e he
    have hp := he
    rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin] at hp
    exact ⟨hp.1, boundaryGluingBetaEdges_subset_leftHatEdges W h k hτ x hq he⟩



theorem boundaryGluingPrimedEdges_inter_rightHatEdges
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    boundaryGluingPrimedEdges W h k hτ ∩ boundaryGluingRightHatEdges W h k hτ x hq =
      boundaryGluingBetaEdges W h k hτ ∩ boundaryGluingHatSeamEdges W h k hτ x hq := by
  apply Set.Subset.antisymm
  · rintro e ⟨hp, hr⟩
    have hb : e ∈ boundaryGluingBetaEdges W h k hτ := by
      rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin]
      obtain ⟨a, ha, he⟩ := hr
      exact ⟨hp, a, he⟩
    refine ⟨hb, ?_⟩
    rw [← boundaryGluingLeftHatEdges_inter_rightHatEdges W h k hτ x hq]
    exact ⟨boundaryGluingBetaEdges_subset_leftHatEdges W h k hτ x hq hb, hr⟩
  · rintro e ⟨hb, hs⟩
    rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin] at hb
    rw [← boundaryGluingLeftHatEdges_inter_rightHatEdges W h k hτ x hq] at hs
    exact ⟨hb.1, hs.2⟩





theorem wholePlane_ae_boundaryGluing_inputs :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ h : BoundaryHitWitnesses (shiftedStream W 0), ∀ k : ℤ,
        ∃ (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
          (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)),
          hatRootedMapClause (boundaryGluingFutureStream W h k) hτ hfin ∧
          ∀ x : XDP, boundaryFutureHattedPath k W ∈
            selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime := by
  have hdomain : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ x : XDP, ∀ k : ℤ,
      boundaryFutureHattedPath k W ∈
        selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime := by
    have hl : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ,
        boundaryFutureHattedPath k W ∈
          selectedCutCoherentDomain .ldp renewalTime renewalTime_positiveSuccessTime :=
      ae_all_iff.mpr (fun k => (boundaryFutureThinSides_package .ldp k).2.2.2.2.2)
    have hs : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ,
        boundaryFutureHattedPath k W ∈
          selectedCutCoherentDomain .sdp renewalTime renewalTime_positiveSuccessTime :=
      ae_all_iff.mpr (fun k => (boundaryFutureThinSides_package .sdp k).2.2.2.2.2)
    filter_upwards [hl, hs] with W hl hs
    intro x
    cases x with
    | ldp => exact hl
    | sdp => exact hs
  filter_upwards [wholePlane_ae_boundaryShift_hatRootedMapHypotheses, hdomain]
    with W hW hdomain
  intro h k
  obtain ⟨hτ, hfin, htrans⟩ := hW h k
  exact ⟨hτ, hfin, hatRootedMapClause_of_left_transient _ hτ hfin (htrans hτ),
    fun x => hdomain x k⟩

section PrefixAttachments



@[expose] noncomputable def boundaryGluingUpperLeftEdges : Set ℕ :=
  {e | e ∈ (kmswStage (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast}



@[expose] noncomputable def boundaryGluingUpperRightEdges : Set ℕ :=
  {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} ∪
    {e | e ∈ (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).UR}

/-- Helper toward Lemma 5.5: an upper-left attachment has a missing
lower-left representative in the fresh future, at every allocating stage. -/
private theorem gluing_window_upperLeft_preimage (w : ℕ → Fin 3) (t e : ℕ)
    (he : kmswWindowEdgeMapInf w t e ∈ (kmswStage w t).UL.dropLast) :
    e ∈ (kmswStage (fun i => w (t + i)) e).LL := by
  let d := kmswWindowPatchData w t e
  have hb := kmsw_edge_allocated_by_self (fun i => w (t + i)) e
  have hr := kmswWindowPatchData_rel w t e
  change KMSWWindowPatchRel _ _ _ d.φ d.A d.B d.YL d.YR d.XL d.XR at hr
  rw [kmswWindowEdgeMapInf_eq_stage w t e e hb] at he
  rw [hr.left_residual] at he
  rcases List.mem_append.mp he with ha | hy
  · exact ((hr.fresh_image e hb).1 ha).elim
  · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hy
    have hfLL : f ∈ (kmswStage (fun i => w (t + i)) e).LL := by
      rw [hr.ll_split]
      exact List.mem_append_right _ hf
    have hfb := (kmswStage_boundary_ids_lt_nextEdge (fun i => w (t + i)) e).2 f
      (by simp only [List.mem_append]; tauto)
    have hfe' := hr.edge_injective f hfb e hb hfe
    exact hfe' ▸ hfLL



private theorem gluing_LL_not_present (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).LL) : ¬ EdgePresent w e := by
  have hmono {m : ℕ} (hnm : n ≤ m) : e ∈ (kmswStage w m).LL := by
    induction m, hnm using Nat.le_induction with
    | base => exact he
    | succ m _ ih =>
      change e ∈ (kmswStep (kmswStage w m) (w m)).LL
      unfold kmswStep
      cases hc : kmswCodeStep (w m) with
      | up => exact ih
      | down => cases hs : (kmswStage w m).UR <;>
          simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | left =>
        cases hs : (kmswStage w m).UL.dropLast.reverse with
        | nil =>
          simpa only [kmswStepOfStep, hs, State.addEdge] using
            List.mem_cons_of_mem ((kmswStage w m).nextEdge + 1) ih
        | cons f fs => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
  intro hp
  obtain ⟨m, hm⟩ := hp.eventually_present
  have hm' := hm (max m n) (Nat.le_max_left _ _)
  have hmissing := ((kmswStage_status w (max m n)).1 e hm'.1).mpr
    (Or.inr (hmono (Nat.le_max_right _ _)))
  rw [hm'.2] at hmissing
  cases hmissing

include hτ in


theorem boundaryGluingPrefixEdges_inter_futureRange :
    boundaryGluingPrefixEdges W h k ∩ Set.range (boundaryGluingEdgeMap W h k) =
      boundaryGluingUpperLeftEdges W h k ∪ boundaryGluingUpperRightEdges W h k := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let hb := hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ
  have hupper (e : ℕ) :
      e ∈ (kmswStage w t).UL ++ (kmswStage w t).UR ↔
        e ∈ boundaryGluingUpperLeftEdges W h k ∪
          boundaryGluingUpperRightEdges W h k := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last w t
    change (e ∈ (kmswStage w t).UL ++ (kmswStage w t).UR) ↔
      (e ∈ (kmswStage w t).UL.dropLast ∨
        e ∈ ({act w t} : Set ℕ) ∪ {e | e ∈ (kmswStage w t).UR})
    rw [hes, List.dropLast_concat]
    simp only [List.mem_append, List.mem_singleton, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_ofPred_eq, act]
    tauto
  apply Set.Subset.antisymm
  · rintro e ⟨he, f, rfl⟩
    exact (hupper _).mp (kmswWindowEdgeMapInf_old_mem_upper w t f he)
  · intro e he
    have hu := (hupper e).mpr he
    refine ⟨(kmswStage_boundary_ids_lt_nextEdge w t).2 e ?_, ?_⟩
    · simp only [List.mem_append] at hu ⊢
      tauto
    · exact kmswWindowEdgeMapInf_range_upper w t hb e hu



theorem boundaryGluingUpperLeftEdges_disjoint_hatRange :
    Disjoint (boundaryGluingUpperLeftEdges W h k)
      (Set.range (boundaryGluingHatEdgeMap W h k hτ)) := by
  apply Set.disjoint_left.mpr
  rintro e he ⟨a, rfl⟩
  let u := boundaryGluingFutureStream W h k
  have hLL := gluing_window_upperLeft_preimage (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k) (hatLimitEdgeMap u hτ a) he
  have hp := (hatLimitEdgeMap_range_iff u hτ _).mp ⟨a, rfl⟩
  exact gluing_LL_not_present u _ _ hLL hp.1

include hfin in


theorem boundaryGluingUpperLeftEdges_subset_primedEdges :
    boundaryGluingUpperLeftEdges W h k ⊆ boundaryGluingPrimedEdges W h k hτ := by
  intro e he
  have hu : e ∈ Set.range (boundaryGluingEdgeMap W h k) := by
    have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := by
      rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ]
      exact Or.inl he
    exact hm.2
  obtain ⟨f, rfl⟩ := hu
  let u := boundaryGluingFutureStream W h k
  have hn : ¬ MhatGeometricEdge u f := by
    intro hf
    obtain ⟨a, ha⟩ := (hatLimitEdgeMap_geometric_range_iff u hτ f).mpr hf
    apply Set.disjoint_left.mp (boundaryGluingUpperLeftEdges_disjoint_hatRange W h k hτ)
      he
    exact ⟨a, congrArg (boundaryGluingEdgeMap W h k) ha⟩
  obtain ⟨a, ha⟩ := (primeGeomEdge_iff_primedLimitEdge u hfin
    (hatBoundaryHitWitnesses u hτ) hτ f).mp (Or.inl hn)
  exact ⟨a, congrArg (boundaryGluingEdgeMap W h k) ha⟩



theorem boundaryGluingUpperRightEdges_of_nonneg (hk : 0 ≤ k) :
    boundaryGluingUpperRightEdges W h k =
      {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} := by
  have hUR : (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).UR = [] := by
    by_cases hk0 : k = 0
    · subst k
      rw [boundaryHitTime_zero]
      rfl
    · exact boundaryHit_right_UR_empty _ h (by omega)
  simp only [boundaryGluingUpperRightEdges, hUR, List.not_mem_nil,
    Set.ofPred_false, Set.union_empty]



theorem boundaryGluing_active_not_mem_upperLeft :
    act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) ∉
      boundaryGluingUpperLeftEdges W h k := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  obtain ⟨es, hes⟩ := kmswStage_UL_last w t
  have hnd : (kmswStage w t).UL.Nodup := by
    rw [kmswStage_UL_eq]
    exact (List.Nodup.filter _ List.nodup_range).map (CutConverse.act_injective w)
  rw [hes] at hnd
  change act w t ∉ (kmswStage w t).UL.dropLast
  rw [hes, List.dropLast_concat]
  intro he
  exact (List.nodup_append.mp hnd).2.2 _ he _ (List.mem_singleton_self _) rfl

include hτ in


theorem boundaryGluingPrefixMinusEdges_inter_futureRange (hk : 0 ≤ k) :
    boundaryGluingPrefixMinusEdges W h k ∩ Set.range (boundaryGluingEdgeMap W h k) =
      boundaryGluingUpperLeftEdges W h k := by
  ext e
  constructor
  · rintro ⟨he, hu⟩
    have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := ⟨he.1, hu⟩
    rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ,
      boundaryGluingUpperRightEdges_of_nonneg W h k hk] at hm
    exact hm.resolve_right he.2
  · intro he
    have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := by
      rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ]
      exact Or.inl he
    exact ⟨⟨hm.1, fun heq => boundaryGluing_active_not_mem_upperLeft W h k (heq ▸ he)⟩,
      hm.2⟩

include hfin in


theorem boundaryGluingPrefixMinusEdges_inter_primedEdges (hk : 0 ≤ k) :
    boundaryGluingPrefixMinusEdges W h k ∩ boundaryGluingPrimedEdges W h k hτ =
      boundaryGluingUpperLeftEdges W h k := by
  apply Set.Subset.antisymm
  · rintro e ⟨he, a, rfl⟩
    rw [← boundaryGluingPrefixMinusEdges_inter_futureRange W h k hτ hk]
    exact ⟨he, _, rfl⟩
  · intro e he
    have hm : e ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := by
      rw [boundaryGluingPrefixMinusEdges_inter_futureRange W h k hτ hk]
      exact he
    exact ⟨hm.1, boundaryGluingUpperLeftEdges_subset_primedEdges W h k hτ hfin he⟩



theorem boundaryGluingPrefixMinusEdges_inter_hatRange (hk : 0 ≤ k) :
    boundaryGluingPrefixMinusEdges W h k ∩ Set.range (boundaryGluingHatEdgeMap W h k hτ) =
      ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨he, a, rfl⟩
  have hm : boundaryGluingHatEdgeMap W h k hτ a ∈
      boundaryGluingPrefixMinusEdges W h k ∩ Set.range (boundaryGluingEdgeMap W h k) :=
    ⟨he, _, rfl⟩
  rw [boundaryGluingPrefixMinusEdges_inter_futureRange W h k hτ hk] at hm
  exact Set.disjoint_left.mp (boundaryGluingUpperLeftEdges_disjoint_hatRange W h k hτ)
    hm ⟨a, rfl⟩



theorem boundaryGluingPrefixMinusEdges_inter_hatSideEdges (hk : 0 ≤ k) (s : ThinMapSide) :
    boundaryGluingPrefixMinusEdges W h k ∩ boundaryGluingHatSideEdges W h k hτ x hq s =
      ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨he, a, ha, rfl⟩
  have hm : boundaryGluingHatEdgeMap W h k hτ a ∈
      boundaryGluingPrefixMinusEdges W h k ∩ Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
    ⟨he, a, rfl⟩
  rw [boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk] at hm
  exact hm



theorem boundaryGluingHatEdgeMap_zero :
    boundaryGluingHatEdgeMap W h k hτ 0 =
      act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) := by
  change boundaryGluingEdgeMap W h k
    (hatLimitEdgeMap (boundaryGluingFutureStream W h k) hτ 0) = _
  rw [hatLimitEdgeMap_zero]
  change kmswWindowEdgeMapInf (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k) 0 = _
  rw [kmswWindowEdgeMapInf_eq_stage _ _ 0 0 (by change 0 < 1; omega)]
  exact (kmswWindowPatchData_rel _ _ 0).root



theorem boundaryGluing_active_mem_rightHatEdges :
    act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) ∈
      boundaryGluingRightHatEdges W h k hτ x hq := by
  refine ⟨0, ?_, boundaryGluingHatEdgeMap_zero W h k hτ⟩
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  let z := boltzmannKMSWStream (pathCode q.1)
  let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
  let hL := sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q
  let ht := sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q
  let hR := sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q
  change 0 ∈ ⋃ i, geometricAncestorEdges x renewalTime
    renewalTime_positiveSuccessTime .right q i
  rw [iUnion_geometricAncestorEdges]
  have he : (kmswRightmostPath z hf hL ht hR 0).edge 0 = 0 := by
    change kmswRightmostOutgoingEdge z hf hL ht hR
      (kmsw_vertex_allocated_of_finite_incidence z hf) 0 = 0
    rw [kmswRightmostOutgoingEdge_source, kmswRightBoundaryEdge_zero]
  have hb := rightBoundaryTrace_subset_sideRegion z hf hL ht hR
    (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q)
  intro p hp
  apply hb
  exact Set.mem_iUnion.mpr ⟨0, by
    change p ∈ ((monotoneFamilyDrawing z hf (monotone_family_all z)).arc
      ((kmswRightmostPath z hf hL ht hR 0).edge 0, false)).image
    rw [he]
    exact hp⟩



theorem boundaryGluingPrefixEdges_inter_rightHatEdges (hk : 0 ≤ k) :
    boundaryGluingPrefixEdges W h k ∩ boundaryGluingRightHatEdges W h k hτ x hq =
      {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} := by
  apply Set.Subset.antisymm
  · rintro e ⟨he, a, ha, hea⟩
    by_contra hn
    have hm : e ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) := ⟨⟨he, hn⟩, a, hea⟩
    rw [boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk] at hm
    exact hm
  · rintro e rfl
    exact ⟨boundaryGluing_active_mem_prefix W h k,
      boundaryGluing_active_mem_rightHatEdges W h k hτ x hq⟩



theorem boundaryGluingPrefixEdges_inter_leftHatEdges (hk : 0 ≤ k) :
    boundaryGluingPrefixEdges W h k ∩ boundaryGluingLeftHatEdges W h k hτ x hq =
      {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} ∩
        boundaryGluingHatSeamEdges W h k hτ x hq := by
  apply Set.Subset.antisymm
  · rintro e ⟨he, hl⟩
    have heq : e = act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) := by
      by_contra hn
      obtain ⟨a, ha, hea⟩ := hl
      have hm : e ∈ boundaryGluingPrefixMinusEdges W h k ∩
          Set.range (boundaryGluingHatEdgeMap W h k hτ) := ⟨⟨he, hn⟩, a, hea⟩
      rw [boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk] at hm
      exact hm
    refine ⟨heq, ?_⟩
    rw [← boundaryGluingLeftHatEdges_inter_rightHatEdges W h k hτ x hq]
    exact ⟨hl, heq.symm ▸ boundaryGluing_active_mem_rightHatEdges W h k hτ x hq⟩
  · rintro e ⟨rfl, hs⟩
    exact ⟨boundaryGluing_active_mem_prefix W h k,
      (boundaryGluingHatSeamEdges_subset_both W h k hτ x hq hs).1⟩

include hfin in



theorem boundaryGluingPrefixEdges_inter_primedEdges (hk : 0 ≤ k) :
    boundaryGluingPrefixEdges W h k ∩ boundaryGluingPrimedEdges W h k hτ =
      boundaryGluingUpperLeftEdges W h k ∪
        ({act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} ∩
          boundaryGluingBetaEdges W h k hτ) := by
  apply Set.Subset.antisymm
  · rintro e ⟨he, hp⟩
    by_cases heq : e = act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
    · right
      refine ⟨heq, ?_⟩
      rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin]
      exact ⟨hp, 0, (boundaryGluingHatEdgeMap_zero W h k hτ).trans heq.symm⟩
    · left
      rw [← boundaryGluingPrefixMinusEdges_inter_primedEdges W h k hτ hfin hk]
      exact ⟨⟨he, heq⟩, hp⟩
  · rintro e (he | ⟨rfl, hb⟩)
    · have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
          Set.range (boundaryGluingEdgeMap W h k) := by
        rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ]
        exact Or.inl he
      exact ⟨hm.1, boundaryGluingUpperLeftEdges_subset_primedEdges W h k hτ hfin he⟩
    · rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin] at hb
      exact ⟨boundaryGluing_active_mem_prefix W h k, hb.1⟩

/-- Helper toward Lemma 5.5: every lower-right boundary edge of a
nonnegative transient code belongs to the literal right geometric side. -/
private theorem gluing_rightBoundary_mem_sideEdges (z : ℕ → Fin 3)
    (hf : KMSWFiniteIncidence z) (hL : ∀ n, 0 ≤ L z n)
    (ht : Filter.Tendsto (L z) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R z n ≤ a) (P : InfinitePresentPath z ⟨0⟩) (i : ℕ) :
    kmswRightBoundaryEdge z i ∈ sideEdges z hf hL ht hR P .right := by
  let B := kmswRightmostPath z hf hL ht hR 0
  have he (j : ℕ) : B.edge j = kmswRightBoundaryEdge z j := by
    induction j with
    | zero =>
      change kmswRightmostOutgoingEdge z hf hL ht hR
        (kmsw_vertex_allocated_of_finite_incidence z hf) 0 = _
      exact kmswRightmostOutgoingEdge_source z hf hL ht hR _
    | succ j ih =>
      have hv : kmswRightmostOrbit z hf hL ht hR 0 (j + 1) =
          edgeWest z (kmswRightBoundaryEdge z (j + 1)) := by
        rw [← (kmswRightmostPath_edge_spec z hf hL ht hR 0 j).2.2, ih]
        exact (kmswRightBoundary_infinite_path z hL hR).2.1 j
      change kmswRightmostOutgoingEdge z hf hL ht hR _
        (kmswRightmostOrbit z hf hL ht hR 0 (j + 1)) = _
      rw [hv]
      exact kmswRightBoundaryEdge_is_rightmost z hf hL ht hR (by omega)
  intro p hp
  apply rightBoundaryTrace_subset_sideRegion z hf hL ht hR P
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  change p ∈ ((monotoneFamilyDrawing z hf (monotone_family_all z)).arc
    (B.edge i, false)).image
  rw [he]
  exact hp

/-- Helper toward Lemma 5.5: the lower-right boundary is retained by
the hatted map as its lower-right boundary. This uses the actual unbounded
faces of the two drawings, including the geometric dart side. -/
private theorem gluing_hat_preimage_of_LR (u : ℕ → Fin 3) (hu : HasFlowLineHits u)
    (hf : hatLimitFiniteIncidence u)
    (hL : ∀ n, 0 ≤ L (hatCodes u hu) n)
    (ht : Filter.Tendsto (L (hatCodes u hu)) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R (hatCodes u hu) n ≤ a)
    (n e : ℕ) (he : e ∈ (kmswStage u n).LR) :
    ∃ i, hatLimitEdgeMap u hu (kmswRightBoundaryEdge (hatCodes u hu) i) = e := by
  let hb := hatBoundaryHitWitnesses u hu
  have hm {m : ℕ} (hnm : n ≤ m) : e ∈ (kmswStage u m).LR := by
    induction m, hnm using Nat.le_induction with
    | base => exact he
    | succ m _ ih =>
      obtain ⟨l, hl⟩ := kmswStage_LR_succ_eq_append u m
      rw [hl]
      exact List.mem_append_left _ ih
  have hej : e ∈ Set.range (kmswRightBoundaryEdge u) := by
    rw [← kmswRunEventuallyLR_eq_range u hb]
    exact ⟨n, fun m hnm => hm hnm⟩
  obtain ⟨j, hj⟩ := hej
  have houter : boundaryOuterEdge u hb (j : ℤ) = e := by
    by_cases hj0 : j = 0
    · subst j
      simpa only [Nat.cast_zero, boundaryOuterEdge_zero, kmswRightBoundaryEdge_zero]
        using hj
    · rw [boundaryOuterEdge_of_positive u hb (by omega)]
      simpa only [Int.toNat_natCast] using hj
  have hends := boundaryOuterEdge_endpoints u hb (j : ℤ)
  rw [houter] at hends
  have hgeom : MhatGeometricEdge u e := by
    constructor
    · rw [hends.1]
      change Quiver.Reachable (⟨0⟩ : PresentVertex u) ⟨boundaryVertex u hb (j : ℤ)⟩
      simpa only [boundaryVertex_zero] using
        boundaryVertex_nonneg_reachable u hb (k := 0) (l := (j : ℤ)) le_rfl (by omega)
    · rw [hends.2.1]
      change Quiver.Reachable (⟨0⟩ : PresentVertex u) ⟨boundaryVertex u hb ((j : ℤ) + 1)⟩
      simpa only [boundaryVertex_zero] using
        boundaryVertex_nonneg_reachable u hb (k := 0) (l := (j : ℤ) + 1) le_rfl (by omega)
  obtain ⟨a, ha⟩ := (hatLimitEdgeMap_geometric_range_iff u hu e).mpr hgeom
  have hext : limitExternalDart u (e, true) := by
    apply (limitExternalDart_iff_upper_or_lower u (e, true)).mpr
    right
    refine ⟨n, fun m hnm => ⟨rfl, ?_, List.mem_append_right _ (hm hnm)⟩⟩
    exact (kmswStage_boundary_ids_lt_nextEdge u m).2 e (by
      simp only [List.mem_append]; tauto)
  let P := monotoneFamilyDrawing u hf (monotone_family_all u)
  let Q := hatRealizedDrawing u hf
  obtain ⟨E, U, hE, hEU, hU, _⟩ := hatRealizedFaces_unbounded_root_face u hu hf
  obtain ⟨E', _, huniq, hborder⟩ :=
    monotoneFamilyDrawing_faceClassification_twoSided u hf hb
  have hd : P.dartBorders (e, true) E := by
    rw [huniq E hE]
    exact (hborder (e, true)).mpr hext
  have hdQ : Q.dartBorders (hatLimitDartEquiv u hu (a, true)) U := by
    obtain ⟨δ, hδ, hd⟩ := hd
    refine ⟨δ, hδ, ?_⟩
    intro t ε ht' htδ hε hεδ
    have harc : Q.arc (hatLimitDartEquiv u hu (a, true)) = P.arc (e, true) := by
      rw [restrictDrawing_arc, hatLimitDartEquiv_apply]
      change P.arc (hatLimitEdgeMap u hu a, true) = P.arc (e, true)
      rw [ha]
    rw [harc]
    exact hEU (hd t ε ht' htδ hε hεδ)
  have hextHat := hatRealizedFaces_unbounded_border_external u hu hf U hU (a, true) hdQ
  rcases (limitExternalDart_iff (hatCodes u hu) ht hR hL (a, true)).mp hextHat with
    ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Bool.noConfusion (congrArg Prod.snd hi)
  · exact ⟨i, (congrArg (hatLimitEdgeMap u hu) (congrArg Prod.fst hi)).symm.trans ha⟩

/-- Helper toward Lemma 5.5: an upper-right stopped edge other than
the active root has a lower-right boundary representative in the future. -/
private theorem gluing_window_UR_preimage (w : ℕ → Fin 3) (t e : ℕ)
    (he : kmswWindowEdgeMapInf w t e ∈ (kmswStage w t).UR) :
    e ∈ (kmswStage (fun i => w (t + i)) e).LR := by
  let d := kmswWindowPatchData w t e
  have hb := kmsw_edge_allocated_by_self (fun i => w (t + i)) e
  have hr := kmswWindowPatchData_rel w t e
  change KMSWWindowPatchRel _ _ _ d.φ d.A d.B d.YL d.YR d.XL d.XR at hr
  rw [kmswWindowEdgeMapInf_eq_stage w t e e hb, hr.right_residual] at he
  rcases List.mem_append.mp he with hy | hb'
  · obtain ⟨f, hf', hfe⟩ := List.mem_map.mp hy
    have hfLR : f ∈ (kmswStage (fun i => w (t + i)) e).LR := by
      rw [hr.lr_split]
      exact List.mem_append_left _ (List.mem_append_right _ hf')
    have hfb := (kmswStage_boundary_ids_lt_nextEdge (fun i => w (t + i)) e).2 f
      (by simp only [List.mem_append]; tauto)
    exact hr.edge_injective f hfb e hb hfe ▸ hfLR
  · exact ((hr.fresh_image e hb).2 hb').elim

include hfin in


theorem boundaryGluingUpperRightEdges_subset_rightHatEdges :
    boundaryGluingUpperRightEdges W h k ⊆ boundaryGluingRightHatEdges W h k hτ x hq := by
  rintro e (rfl | he)
  · exact boundaryGluing_active_mem_rightHatEdges W h k hτ x hq
  · have hu : e ∈ Set.range (boundaryGluingEdgeMap W h k) :=
      kmswWindowEdgeMapInf_range_upper (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)
        (hatBoundaryHitWitnesses (boundaryGluingFutureStream W h k) hτ) e
        (List.mem_append_right _ he)
    obtain ⟨f, rfl⟩ := hu
    let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
      ⟨boundaryFutureHattedPath k W, hq⟩
    let u := boundaryGluingFutureStream W h k
    have hLL := gluing_window_UR_preimage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k) f he
    have hc := boundaryGluing_decoded_stream W h k hτ
    have hL := sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q
    have ht := sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q
    have hR := sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q
    rw [hc] at hL ht hR
    obtain ⟨i, hi⟩ := gluing_hat_preimage_of_LR u hτ hfin hL ht hR f f hLL
    refine ⟨kmswRightBoundaryEdge (hatCodes u hτ) i, ?_,
      congrArg (boundaryGluingEdgeMap W h k) hi⟩
    change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
      renewalTime_positiveSuccessTime .right q j
    rw [iUnion_geometricAncestorEdges, ← hc]
    exact gluing_rightBoundary_mem_sideEdges _ _ _ _ _ _ i

include hfin in


theorem boundaryGluingPrefixEdges_inter_rightHatEdges_eq_upperRight :
    boundaryGluingPrefixEdges W h k ∩ boundaryGluingRightHatEdges W h k hτ x hq =
      boundaryGluingUpperRightEdges W h k := by
  apply Set.Subset.antisymm
  · rintro e ⟨he, a, ha, hea⟩
    have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := ⟨he, _, hea⟩
    rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ] at hm
    rcases hm with hl | hr
    · exact (Set.disjoint_left.mp
        (boundaryGluingUpperLeftEdges_disjoint_hatRange W h k hτ) hl ⟨a, hea⟩).elim
    · exact hr
  · intro e he
    have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := by
      rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ]
      exact Or.inr he
    exact ⟨hm.1, boundaryGluingUpperRightEdges_subset_rightHatEdges W h k hτ x hq hfin he⟩

include hfin in


theorem boundaryGluingPrefixEdges_inter_leftHatEdges_eq_upperRight_inter_seam :
    boundaryGluingPrefixEdges W h k ∩ boundaryGluingLeftHatEdges W h k hτ x hq =
      boundaryGluingUpperRightEdges W h k ∩ boundaryGluingHatSeamEdges W h k hτ x hq := by
  apply Set.Subset.antisymm
  · rintro e ⟨he, hl⟩
    obtain ⟨a, ha, hea⟩ := hl
    have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := ⟨he, _, hea⟩
    rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ] at hm
    have hr : e ∈ boundaryGluingUpperRightEdges W h k := by
      rcases hm with hu | hu
      · exact (Set.disjoint_left.mp
          (boundaryGluingUpperLeftEdges_disjoint_hatRange W h k hτ) hu ⟨a, hea⟩).elim
      · exact hu
    refine ⟨hr, ?_⟩
    rw [← boundaryGluingLeftHatEdges_inter_rightHatEdges W h k hτ x hq]
    exact ⟨⟨a, ha, hea⟩,
      boundaryGluingUpperRightEdges_subset_rightHatEdges W h k hτ x hq hfin hr⟩
  · rintro e ⟨he, hs⟩
    have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
        boundaryGluingRightHatEdges W h k hτ x hq := by
      rw [boundaryGluingPrefixEdges_inter_rightHatEdges_eq_upperRight W h k hτ x hq hfin]
      exact he
    exact ⟨hm.1, (boundaryGluingHatSeamEdges_subset_both W h k hτ x hq hs).1⟩

include hfin x hq in



theorem boundaryGluingPrefixEdges_inter_primedEdges_eq_upperLeft_union_beta :
    boundaryGluingPrefixEdges W h k ∩ boundaryGluingPrimedEdges W h k hτ =
      boundaryGluingUpperLeftEdges W h k ∪
        (boundaryGluingUpperRightEdges W h k ∩ boundaryGluingBetaEdges W h k hτ) := by
  apply Set.Subset.antisymm
  · rintro e ⟨he, hp⟩
    obtain ⟨a, ha⟩ := hp
    have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := ⟨he, _, ha⟩
    rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ] at hm
    rcases hm with hl | hr
    · exact Or.inl hl
    · right
      refine ⟨hr, ?_⟩
      rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin]
      obtain ⟨b, hb, hbe⟩ :=
        boundaryGluingUpperRightEdges_subset_rightHatEdges W h k hτ x hq hfin hr
      exact ⟨⟨a, ha⟩, b, hbe⟩
  · rintro e (hl | ⟨hr, hb⟩)
    · have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
          Set.range (boundaryGluingEdgeMap W h k) := by
        rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ]
        exact Or.inl hl
      exact ⟨hm.1, boundaryGluingUpperLeftEdges_subset_primedEdges W h k hτ hfin hl⟩
    · have hm : e ∈ boundaryGluingPrefixEdges W h k ∩
          Set.range (boundaryGluingEdgeMap W h k) := by
        rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ]
        exact Or.inr hr
      rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin] at hb
      exact ⟨hm.1, hb.1⟩

/-- Helper toward Lemma 5.5: deleting the active edge commutes with
restriction to any geometric carrier. -/
private theorem gluing_delete_inter (A B : Set ℕ) (a : ℕ) :
    (A \ {a}) ∩ B = (A ∩ B) \ {a} := by
  ext e
  change (e ∈ A ∧ e ∉ ({a} : Set ℕ)) ∧ e ∈ B ↔
    (e ∈ A ∧ e ∈ B) ∧ e ∉ ({a} : Set ℕ)
  tauto

include hfin in


theorem boundaryGluingPrefixMinusEdges_inter_rightHatEdges_eq_upperRight_sdiff :
    boundaryGluingPrefixMinusEdges W h k ∩ boundaryGluingRightHatEdges W h k hτ x hq =
      boundaryGluingUpperRightEdges W h k \
        {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} := by
  rw [boundaryGluingPrefixMinusEdges, gluing_delete_inter,
    boundaryGluingPrefixEdges_inter_rightHatEdges_eq_upperRight W h k hτ x hq hfin]

include hfin in



theorem boundaryGluingPrefixMinusEdges_inter_leftHatEdges_eq_upperRight_inter_seam_sdiff :
    boundaryGluingPrefixMinusEdges W h k ∩ boundaryGluingLeftHatEdges W h k hτ x hq =
      (boundaryGluingUpperRightEdges W h k ∩ boundaryGluingHatSeamEdges W h k hτ x hq) \
        {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} := by
  rw [boundaryGluingPrefixMinusEdges, gluing_delete_inter,
    boundaryGluingPrefixEdges_inter_leftHatEdges_eq_upperRight_inter_seam W h k hτ x hq hfin]

include hfin x hq in



theorem boundaryGluingPrefixMinusEdges_inter_primedEdges_eq_upperLeft_union_beta_sdiff :
    boundaryGluingPrefixMinusEdges W h k ∩ boundaryGluingPrimedEdges W h k hτ =
      (boundaryGluingUpperLeftEdges W h k ∪
        (boundaryGluingUpperRightEdges W h k ∩ boundaryGluingBetaEdges W h k hτ)) \
        {act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)} := by
  rw [boundaryGluingPrefixMinusEdges, gluing_delete_inter,
    boundaryGluingPrefixEdges_inter_primedEdges_eq_upperLeft_union_beta W h k hτ x hq hfin]

end PrefixAttachments

/- The path-transport API uses the all-times edge map, while the geometric
carriers above use the window map. This comparison includes missing edges. -/



private theorem boundaryGluing_shift_edge_eq_window (w : ℕ → Fin 3) (t m e : ℕ)
    (he : e < (kmswStage (fun i => w (t + i)) m).nextEdge) :
    kmswShiftEdgeMapAll w t m e = (kmswWindowPatchData w t m).φ e := by
  induction m with
  | zero => rfl
  | succ m ih =>
    let F := kmswStage (fun i => w (t + i)) m
    let G := kmswStage w (t + m)
    let D := kmswWindowPatchData w t m
    have hrel := kmswWindowPatchData_rel w t m
    change KMSWWindowPatchRel _ G F D.φ D.A D.B D.YL D.YR D.XL D.XR at hrel
    by_cases hold : e < F.nextEdge
    · rw [kmswShiftEdgeMapAll_extend w t m e hold,
        kmswWindowPatchData_extends w t m e hold]
      exact ih hold
    have hge : F.nextEdge ≤ e := by omega
    change e < (kmswStep F ((fun i => w (t + i)) m)).nextEdge at he
    change kmswShiftNextEdgeMap F G (kmswCodeStep (w (t + m)))
      (kmswShiftEdgeMapAll w t m) e =
      (KMSWWindowPatchData.step G F (kmswCodeStep (w (t + m))) D).φ e
    cases hc : kmswCodeStep (w (t + m)) with
    | up =>
      have hb : e = F.nextEdge ∨ e = F.nextEdge + 1 := by
        simp only [kmswStep, hc, kmswStepOfStep, State.addEdge] at he
        omega
      rcases hb with rfl | rfl <;>
        simp [kmswShiftNextEdgeMap, kmswShiftUpEdgeMap, KMSWWindowPatchData.step]
    | down =>
      cases hf : F.UR with
      | cons q qs => simp only [kmswStep, hc, kmswStepOfStep, hf] at he; omega
      | nil =>
        have heq : e = F.nextEdge := by
          simp only [kmswStep, hc, kmswStepOfStep, hf, State.addEdge] at he
          omega
        subst e
        have hg : G.UR = D.B := by simpa only [hf, List.map_nil, List.nil_append]
          using hrel.ur
        cases hb : D.B <;>
          simp [kmswShiftNextEdgeMap, hf, hg, hb, kmswShiftFreshEdgeMap,
            kmswShiftDownMismatchEdgeMap, KMSWWindowPatchData.step]
    | left =>
      cases hf : F.UL.dropLast.reverse with
      | cons q qs =>
        have heq : e = F.nextEdge := by
          simp only [kmswStep, hc, kmswStepOfStep, hf, State.addEdge] at he
          omega
        subst e
        simp [kmswShiftNextEdgeMap, hf, kmswShiftFreshEdgeMap,
          KMSWWindowPatchData.step]
      | nil =>
        have hb : e = F.nextEdge ∨ e = F.nextEdge + 1 := by
          simp only [kmswStep, hc, kmswStepOfStep, hf, State.addEdge] at he
          omega
        obtain ⟨xs, hxs⟩ := kmswStage_UL_last (fun i => w (t + i)) m
        have hF : F.UL = [F.active] := by
          have hx : xs = [] := by simpa only [F, hxs, List.dropLast_concat,
            List.reverse_eq_nil_iff] using hf
          simpa only [hx, List.nil_append] using hxs
        have hg : G.UL.dropLast.reverse = D.A.reverse := by
          rw [hrel.ul, hF, List.map_singleton, List.dropLast_concat]
        cases ha : D.A.reverse <;> rcases hb with rfl | rfl <;>
          simp [kmswShiftNextEdgeMap, hf, hg, ha, kmswShiftUpEdgeMap,
            kmswShiftLeftMismatchEdgeMap, KMSWWindowPatchData.step]



theorem boundaryGluingEdgeMap_eq_shift (e : ℕ) :
    boundaryGluingEdgeMap W h k e = kmswShiftEdgeMapAll (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k) e e :=
  (boundaryGluing_shift_edge_eq_window (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k) e e
    (kmsw_edge_allocated_by_self _ e)).symm



theorem boundaryGluing_sourceAncestorPath_segments (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime) :
    let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
    if longest then Q.HasLongestSegments else Q.HasShortestSegments := by
  cases longest with
  | false =>
    exact kmswLeftmostSdpPath_hasShortestSegments _ _ _ _ _ _ _
  | true =>
    exact kmswLeftmostLdpPath_hasLongestSegments _ _ _ _ _ _ _





theorem boundaryGluing_exists_embedded_geodesic (longest : Bool)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime) :
    ∃ P : InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      (if longest then P.HasLongestSegments else P.HasShortestSegments) ∧
      ∀ i : ℕ, P.edge i = boundaryGluingHatEdgeMap W h k hτ
        ((sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
          renewalTime renewalTime_positiveSuccessTime
          ⟨boundaryFutureHattedPath k W, hqMode⟩).edge i) := by
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  have hcode := boundaryGluing_decoded_stream W h k hτ
  let Qhat : InfinitePresentPath
      (hatCodes (boundaryGluingFutureStream W h k) hτ) ⟨0⟩ := hcode ▸ Q
  have hQhat : if longest then Qhat.HasLongestSegments else Qhat.HasShortestSegments := by
    have hQ := boundaryGluing_sourceAncestorPath_segments W k longest hqMode
    change (if longest then Q.HasLongestSegments else Q.HasShortestSegments) at hQ
    have hcast {u v : ℕ → Fin 3} (heq : u = v)
        (A : InfinitePresentPath u ⟨0⟩)
        (hA : if longest then A.HasLongestSegments else A.HasShortestSegments) :
        if longest then (heq ▸ A).HasLongestSegments
        else (heq ▸ A).HasShortestSegments := by
      subst v
      exact hA
    exact hcast hcode Q hQ
  have hedge (i : ℕ) : Qhat.edge i = Q.edge i := by
    have hcast {u v : ℕ → Fin 3} (heq : u = v)
        (A : InfinitePresentPath u ⟨0⟩) :
        (heq ▸ A).edge i = A.edge i := by
      subst v
      rfl
    exact hcast hcode Q
  obtain ⟨P, he, _, _, hL, hS⟩ := rawHat_infinitePath_transport (shiftedStream W 0)
    h k hτ (hatLimitExplicitInput (boundaryGluingFutureStream W h k) hτ) Qhat
  refine ⟨P, ?_, ?_⟩
  · cases longest with
    | false => exact hS hQhat
    | true => exact hL hQhat
  · intro i
    rw [congrFun he i, hedge]
    exact (boundaryGluingEdgeMap_eq_shift W h k _).symm





private theorem boundaryGluing_hat_path_lift (u : ℕ → Fin 3)
    (hu : HasFlowLineHits u) (P : InfinitePresentPath u ⟨0⟩) :
    ∃ Q : InfinitePresentPath (hatCodes u hu) ⟨0⟩,
      ∀ n, hatLimitEdgeMap u hu (Q.edge n) = P.edge n := by
  classical
  let z := hatCodes u hu
  let D := hatLimitExplicitInput u hu
  have hex (n : ℕ) : ∃ e : ℕ, EdgePresent z e ∧
      hatLimitEdgeMap u hu e = P.edge n := by
    apply edge_cover D (P.edge_outgoing_at_initial u n).1
    · rw [(P.edge_outgoing_at_initial u n).2]
      exact (P.initial n).2.reachable
    · rw [(P.edge_incoming_at_succ u n).2]
      exact (P.initial (n + 1)).2.reachable
  choose e hp he using hex
  have hi (n : ℕ) := hatLimit_edge_incidence D (hp n)
  have hs : edgeWest z (e 0) = 0 := by
    apply vertex_inj D (kmswVertexAllocated_all z _)
      (kmswVertexAllocated_all z _)
    exact (hi 0).2.1.symm.trans
      ((congrArg (edgeWest u) (he 0)).trans
        ((P.first_edge_outgoing u).2.trans D.root.symm))
  have hc (n : ℕ) : edgeEast z (e n) = edgeWest z (e (n + 1)) := by
    apply vertex_inj D (kmswVertexAllocated_all z _)
      (kmswVertexAllocated_all z _)
    exact (hi n).2.2.symm.trans
      ((congrArg (edgeEast u) (he n)).trans
        ((P.edge_incoming_at_succ u n).2.trans
          ((P.edge_outgoing_at_initial u (n + 1)).2.symm.trans
            ((congrArg (edgeWest u) (he (n + 1))).symm.trans
              (hi (n + 1)).2.1))))
  have hprefix (n : ℕ) : ∃ q : Quiver.Path (⟨0⟩ : PresentVertex z)
      ⟨edgeWest z (e n)⟩,
      q.length = n ∧ pathEdgeList q = List.ofFn (fun i : Fin n => e i.val) := by
    induction n with
    | zero =>
      rw [hs]
      exact ⟨.nil, rfl, rfl⟩
    | succ n ih =>
      obtain ⟨q, hlen, hedges⟩ := ih
      let f : (⟨edgeWest z (e n)⟩ : PresentVertex z) ⟶
          ⟨edgeWest z (e (n + 1))⟩ := ⟨e n, hp n, rfl, hc n⟩
      refine ⟨q.cons f, congrArg (· + 1) hlen, ?_⟩
      simp only [pathEdgeList, hedges, List.ofFn_succ', List.concat_eq_append,
        Fin.val_castSucc, Fin.val_last]
      rfl
  choose q hlen hedges using hprefix
  exact ⟨⟨e, fun n => ⟨⟨edgeWest z (e n)⟩, q n⟩, hlen, hedges⟩, he⟩





theorem boundaryGluing_infinitePath_lifts_to_hat
    (P : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k)) :
    ∃ Q : InfinitePresentPath (hatCodes (boundaryGluingFutureStream W h k) hτ) ⟨0⟩,
      ∀ n, boundaryGluingHatEdgeMap W h k hτ (Q.edge n) = P.edge n := by
  obtain ⟨S, hS⟩ := boundary_infinitePath_lifts_to_shifted_limit
    (shiftedStream W 0) h k P
  obtain ⟨Q, hQ⟩ := boundaryGluing_hat_path_lift
    (boundaryGluingFutureStream W h k) hτ S
  refine ⟨Q, fun n => ?_⟩
  change boundaryGluingEdgeMap W h k (hatLimitEdgeMap _ hτ (Q.edge n)) = _
  rw [hQ, boundaryGluingEdgeMap_eq_shift]
  exact (shiftLimitEdge_eq (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k) (S.edge n)
    ⟨S.edge n, (S.edge_outgoing_at_initial _ n).1⟩
    (kmsw_edge_allocated_by_self _ _)).symm.trans (hS n)




theorem boundaryGluing_path_edges_subset_hatRange
    (P : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k)) :
    Set.range P.edge ⊆ Set.range (boundaryGluingHatEdgeMap W h k hτ) := by
  obtain ⟨Q, hQ⟩ := boundaryGluing_infinitePath_lifts_to_hat W h k hτ P
  rintro e ⟨n, rfl⟩
  exact ⟨Q.edge n, hQ n⟩

/-- Helper toward Lemma 5.5: a reversed rotation chain gives interval order. -/
private theorem boundaryGluing_inverse_chain_arc
    (σ : Equiv.Perm (ℕ × Bool)) (p : (ℕ × Bool) → Prop) (es : List ℕ)
    (hc : es.IsChain (fun a b => σ (b, false) = (a, false)))
    (hm : ∀ e ∈ es, p (e, false)) (e f : ℕ)
    (_he : e ∈ es) (hf : f ∈ es) (hle : es.idxOf e ≤ es.idxOf f) :
    RotationArc σ p (f, false) (e, false) := by
  have haux (i j : ℕ) (hj : j < es.length) (hij : i ≤ j) :
      RotationArc σ p (es[j], false) (es[i], false) := by
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      exact RotationArc.refl _ _ _ (hm _ (List.getElem_mem hj))
    | succ j ih =>
      by_cases heq : i = j + 1
      · subst i
        exact RotationArc.refl _ _ _ (hm _ (List.getElem_mem hj))
      have hj' : j < es.length := by omega
      have hs := (List.isChain_iff_getElem.mp hc) j hj
      have ha : RotationArc σ p (es[j + 1], false) (es[j], false) := by
        refine ⟨1, by simpa only [pow_one] using hs, ?_⟩
        intro n hn
        have hn' : n = 0 ∨ n = 1 := by omega
        rcases hn' with rfl | rfl
        · exact hm _ (List.getElem_mem hj)
        · simpa only [pow_one, hs] using hm _ (List.getElem_mem hj')
      exact ha.trans (ih hj' (by omega))
  simpa only [List.getElem_idxOf] using
    haux (es.idxOf e) (es.idxOf f) (List.idxOf_lt_length_of_mem hf) hle

/-- Helper toward Lemma 5.5: a cyclic comparison inside an outgoing interval
is an interval comparison. An incoming geometric dart prevents wraparound. -/
private theorem boundaryGluing_arc_of_cyclic_order {α : Type*} [DecidableEq α]
    (σ : Equiv.Perm α) (s : Finset α) (hc : σ.IsCycleOn (s : Set α))
    (p : α → Prop) (r e f d : α) (hr : r ∈ s) (hd : d ∈ s) (hpd : ¬ p d)
    (harc : RotationArc σ p r f)
    (hcyc : ∃ i j : ℕ, 0 < i ∧ i < j ∧
      (σ : α → α)^[i] r = e ∧ (σ : α → α)^[j] r = f ∧
      ∀ n : ℕ, 0 < n → n ≤ j → (σ : α → α)^[n] r ≠ r) :
    RotationArc σ p e f := by
  obtain ⟨i, j, hi, hij, hei, hfj, hno⟩ := hcyc
  change (σ ^ i) r = e at hei
  change (σ ^ j) r = f at hfj
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨r, hr⟩
  have hj : j < s.card := by
    by_contra hh
    exact hno s.card hpos (by omega) (hc.pow_card_apply hr)
  obtain ⟨m, hm, hp⟩ := harc
  obtain ⟨q, hq, hqd⟩ := hc.exists_pow_eq hr hd
  have hm' : m < s.card := by
    by_contra hh
    exact hpd (hqd ▸ hp q (by omega))
  have hmj : m = j := hc.injOn_pow_apply hr hm' hj (hm.trans hfj.symm)
  subst m
  refine ⟨j - i, ?_, ?_⟩
  · rw [← hei, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
    exact hfj
  · intro n hn
    rw [← hei, ← Equiv.Perm.mul_apply, ← pow_add]
    exact hp (n + i) (by omega)

/-- Helper toward Lemma 5.5: outgoing source lists, anchored at the boundary
hit, preserve their linear order in the actual raw drawing. -/
private theorem boundaryGluing_source_list_arg_pairwise
    (hfin : KMSWFiniteIncidence (shiftedStream W 0))
    (hfinS : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hL : ∀ n, 0 ≤ L (hatCodes (boundaryGluingFutureStream W h k) hτ) n)
    (htrans : Filter.Tendsto (L (hatCodes (boundaryGluingFutureStream W h k) hτ))
      Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R (hatCodes (boundaryGluingFutureStream W h k) hτ) n ≤ a) :
    let w := shiftedStream W 0
    let u := boundaryGluingFutureStream W h k
    let z := hatCodes u hτ
    let hf := hatCodes_inducedFiniteIncidence u hτ hfinS
    let es := (kmsw_source_outgoing_enumeration z hf hL htrans hR).choose
    let G := monotoneFamilyDrawing w hfin (monotone_family_all w)
    es.Pairwise (fun e f =>
      Complex.arg (G.arc (boundaryGluingHatEdgeMap W h k hτ e, false)).initialDirection <
        Complex.arg (G.arc (boundaryGluingHatEdgeMap W h k hτ f, false)).initialDirection) := by
  classical
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let z := hatCodes u hτ
  let hf := hatCodes_inducedFiniteIncidence u hτ hfinS
  let es := (kmsw_source_outgoing_enumeration z hf hL htrans hR).choose
  let φ := boundaryGluingHatEdgeMap W h k hτ
  let G := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let hfam : ∀ n, ∃ A : StageDrawing w n, Nonempty (MonotoneStageInvariant w n A) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  have hs := (kmsw_source_outgoing_enumeration z hf hL htrans hR).choose_spec
  have hzero : 0 < es.length := by
    have hh : es.head? = some (kmswRightBoundaryEdge z 0) := hs.2.1
    cases he : es with
    | nil => simp only [he, List.head?_nil, reduceCtorEq] at hh
    | cons a l => exact Nat.zero_lt_succ _
  have hz : es[0] = 0 := by
    have hh := hs.2.1
    change es.head? = some (kmswRightBoundaryEdge z 0) at hh
    rw [kmswRightBoundaryEdge_zero, List.head?_eq_getElem?,
      List.getElem?_eq_getElem hzero] at hh
    exact Option.some.inj hh
  have hiter (i : ℕ) (hi : i < es.length) :
      (kmswInfRot z hf : _ → _)^[i] (0, false) = (es[i], false) := by
    induction i with
    | zero => simp only [Function.iterate_zero, id_eq, hz]
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact (List.isChain_iff_getElem.mp hs.2.2.2.2) i hi
  have hφ (e : ℕ) : φ e = kmswShiftEdgeMapAll w t
      (hatLimitEdgeMap u hτ e) (hatLimitEdgeMap u hτ e) :=
    boundaryGluingEdgeMap_eq_shift W h k _
  have hroot : φ 0 = act w t := by
    have hh := (shiftHat_source_rightBoundary w t hτ).1
    dsimp only at hh
    rw [kmswRightBoundaryEdge_zero] at hh
    exact (hφ 0).trans hh
  have hinc (i : ℕ) (hi : i < es.length) :
      EdgePresent w (φ es[i]) ∧ edgeWest w (φ es[i]) = boundaryVertex w h k := by
    have he := (hs.2.2.2.1 es[i]).mp (List.getElem_mem hi)
    have hh := shiftHat_edge_incidence w t hτ es[i]
    dsimp only at hh
    erw [← hφ] at hh
    have hv := (shiftHat_source_rightBoundary w t hτ).2
    exact ⟨hh.2.2 he.1, hh.1.trans ((congrArg
      (fun b => limitVertexMap (kmswShiftVertexMapAll w t) u (hatLimitVertexMap u hτ b))
      he.2).trans
      (hv.trans (boundaryVertex_eq_edgeWest_hit w h k).symm))⟩
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hbase := boundaryHit_outgoing_arc w h hfin k (φ es[j]) (hinc j hj).1 (hinc j hj).2
  have harc : RotationArc (kmswInfRot w hfin) (futureMapTail w)
      (φ es[i], false) (φ es[j], false) := by
    by_cases hi0 : i = 0
    · subst i
      rw [hz, hroot]
      exact hbase
    · have hcycHat : ∃ a b : ℕ, 0 < a ∧ a < b ∧
          (kmswInfRot z hf : _ → _)^[a] (0, false) = (es[i], false) ∧
          (kmswInfRot z hf : _ → _)^[b] (0, false) = (es[j], false) ∧
          ∀ n : ℕ, 0 < n → n ≤ b →
            (kmswInfRot z hf : _ → _)^[n] (0, false) ≠ (0, false) := by
        refine ⟨i, j, by omega, hij, hiter i hi, hiter j hj, ?_⟩
        intro n hn hnj heq
        have hnlen : n < es.length := lt_of_le_of_lt hnj hj
        have hne : es[n] = es[0] := by
          rw [hz]
          exact congrArg Prod.fst ((hiter n hnlen).symm.trans heq)
        have hh := hs.1.getElem_inj.mp hne
        omega
      have hcyc := (shiftHatInfRot_cyclicOrder_iff w t hτ hfinS hfin
        (0, false) (es[i], false) (es[j], false)).mp hcycHat
      dsimp only at hcyc
      erw [← hφ 0, ← hφ es[i], ← hφ es[j], hroot] at hcyc
      obtain ⟨d, hd⟩ := Xdp.LeftmostXdpTransport.exists_incoming_geometric w hfin h
        (boundaryVertex w h k)
      let S := kmsw_darts_at_vertex_finite w hfin (boundaryVertex w h k)
      apply boundaryGluing_arc_of_cyclic_order (kmswInfRot w hfin) S.toFinset
        (by simpa only [Set.Finite.coe_toFinset] using
          kmswInfRot_isCycleOn_vertex w hfin (boundaryVertex w h k))
        (futureMapTail w) (act w t, false) (φ es[i], false) (φ es[j], false) (d, true)
        (S.mem_toFinset.mpr (boundaryVertex_eq_edgeWest_hit w h k).symm)
        (S.mem_toFinset.mpr hd) (by
          simp only [futureMapTail, Bool.true_eq_false, false_and, not_false_eq_true])
        hbase hcyc
  have harg := Xdp.LeftmostXdpTransport.outgoingArc_arg_le w hfin hfam
    (boundaryVertex w h k) (φ es[i]) (φ es[j])
    (Xdp.LeftmostXdpTransport.exists_incoming_geometric w hfin h _)
    (hinc i hi).2 harc
  apply lt_of_le_of_ne harg
  intro heq
  have he := congrArg Prod.fst (G.initial_arg_injective (φ es[i], false) (φ es[j], false)
    ((hinc i hi).2.trans (hinc j hj).2.symm) heq)
  have he' := boundaryGluingHatEdgeMap_injective W h k hτ he
  have hh := hs.1.getElem_inj.mp he'
  omega




private theorem boundaryGluing_outgoing_index_arg_le
    (hfin : KMSWFiniteIncidence (shiftedStream W 0))
    (hfinS : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hL : ∀ n, 0 ≤ L (hatCodes (boundaryGluingFutureStream W h k) hτ) n)
    (htrans : Filter.Tendsto (L (hatCodes (boundaryGluingFutureStream W h k) hτ))
      Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R (hatCodes (boundaryGluingFutureStream W h k) hτ) n ≤ a)
    (a e f : ℕ)
    (he : EdgePresent (hatCodes (boundaryGluingFutureStream W h k) hτ) e ∧
      edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) e = a)
    (hf : EdgePresent (hatCodes (boundaryGluingFutureStream W h k) hτ) f ∧
      edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) f = a)
    (hidx :
      let z := hatCodes (boundaryGluingFutureStream W h k) hτ
      let hfH := hatCodes_inducedFiniteIncidence (boundaryGluingFutureStream W h k) hτ hfinS
      let es := kmswOutgoingEdgesLeftToRight z hfH hL htrans hR a
        (kmsw_vertex_allocated_of_finite_incidence z hfH a)
      es.idxOf e ≤ es.idxOf f) :
    let G := monotoneFamilyDrawing (shiftedStream W 0) hfin
      (monotone_family_all (shiftedStream W 0))
    Complex.arg (G.arc (boundaryGluingHatEdgeMap W h k hτ f, false)).initialDirection ≤
      Complex.arg (G.arc (boundaryGluingHatEdgeMap W h k hτ e, false)).initialDirection := by
  classical
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let z := hatCodes u hτ
  let hfH := hatCodes_inducedFiniteIncidence u hτ hfinS
  let ha := kmsw_vertex_allocated_of_finite_incidence z hfH a
  let es := kmswOutgoingEdgesLeftToRight z hfH hL htrans hR a ha
  let φ := boundaryGluingHatEdgeMap W h k hτ
  let G := monotoneFamilyDrawing w hfin (monotone_family_all w)
  change es.idxOf e ≤ es.idxOf f at hidx
  have hem : e ∈ es := (mem_kmswOutgoingEdgesLeftToRight z hfH hL htrans hR a ha e).mpr he
  have hfm : f ∈ es := (mem_kmswOutgoingEdgesLeftToRight z hfH hL htrans hR a ha f).mpr hf
  have hφ (b : ℕ) : φ b = kmswShiftEdgeMapAll w t
      (hatLimitEdgeMap u hτ b) (hatLimitEdgeMap u hτ b) :=
    boundaryGluingEdgeMap_eq_shift W h k _
  by_cases ha0 : a = 0
  · have hpair : es.Pairwise (fun e f =>
        Complex.arg (G.arc (φ f, false)).initialDirection <
          Complex.arg (G.arc (φ e, false)).initialDirection) := by
      unfold es kmswOutgoingEdgesLeftToRight
      rw [dite_eq_left ha0]
      exact List.pairwise_reverse.mpr
        (boundaryGluing_source_list_arg_pairwise W h k hτ hfin hfinS hL htrans hR)
    rcases lt_or_eq_of_le hidx with hlt | heq
    · have hh := List.pairwise_iff_getElem.mp hpair (es.idxOf e) (es.idxOf f)
        (List.idxOf_lt_length_of_mem hem) (List.idxOf_lt_length_of_mem hfm) hlt
      have hh' : Complex.arg (G.arc (φ f, false)).initialDirection <
          Complex.arg (G.arc (φ e, false)).initialDirection := by
        simpa only [List.getElem_idxOf] using hh
      exact hh'.le
    · have hef : e = f := (List.idxOf_inj hem).mp heq
      rw [hef]
  · have hchain : es.IsChain (fun a b => kmswInfRot z hfH (b, false) = (a, false)) := by
      unfold es kmswOutgoingEdgesLeftToRight
      rw [dite_eq_right ha0, List.isChain_reverse]
      exact (kmsw_nonzero_outgoing_enumeration z hfH hL hR a ha ha0
        ).choose_spec.choose_spec.choose_spec.2.2.2.2.1
    have hmark : ∀ b ∈ es, futureMapTail z (b, false) := by
      intro b hb
      exact ⟨rfl, ((mem_kmswOutgoingEdgesLeftToRight z hfH hL htrans hR a ha b).mp hb).1⟩
    have harcHat := boundaryGluing_inverse_chain_arc (kmswInfRot z hfH)
      (futureMapTail z) es hchain hmark e f hem hfm hidx
    have harc := (shiftHat_nonzero_outgoingArc_iff w t hτ hfinS hfin a f e
      (kmswVertexAllocated_all z ⟨a⟩) ha0 hf.1 he.1 hf.2 he.2).mp harcHat
    dsimp only at harc
    erw [← hφ, ← hφ] at harc
    have hinc := shiftHat_edge_incidence w t hτ f
    dsimp only at hinc
    erw [← hφ] at hinc
    let v := limitVertexMap (kmswShiftVertexMapAll w t) u (hatLimitVertexMap u hτ a)
    have hfv : edgeWest w (φ f) = v := hinc.1.trans (congrArg
      (fun b => limitVertexMap (kmswShiftVertexMapAll w t) u (hatLimitVertexMap u hτ b)) hf.2)
    let hfam : ∀ n, ∃ A : StageDrawing w n, Nonempty (MonotoneStageInvariant w n A) :=
      fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
        ((monotone_family_all w) n).choose_spec⟩
    exact Xdp.LeftmostXdpTransport.outgoingArc_arg_le w hfin hfam v (φ f) (φ e)
      (Xdp.LeftmostXdpTransport.exists_incoming_geometric w hfin h v) hfv harc

/-- Helper toward Lemma 5.5: mapping a finite path preserves its length. -/
private theorem boundaryGluing_mapPath_length {u v : ℕ → Fin 3}
    (F : Prefunctor (PresentVertex u) (PresentVertex v))
    {a b : PresentVertex u} (q : Quiver.Path a b) :
    (F.mapPath q).length = q.length := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    simp only [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih]

/-- Helper toward Lemma 5.5: changing endpoint certificates keeps length. -/
private theorem boundaryGluing_path_endpoints {u : ℕ → Fin 3}
    {a b c d : PresentVertex u} (ha : a = c) (hb : b = d)
    (q : Quiver.Path a b) : ∃ r : Quiver.Path c d, r.length = q.length := by
  subst c
  subst d
  exact ⟨q, rfl⟩




theorem boundaryGluing_infiniteGeodesic_lifts_to_hat (longest : Bool)
    (P : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hP : if longest then P.HasLongestSegments else P.HasShortestSegments) :
    ∃ Q : InfinitePresentPath (hatCodes (boundaryGluingFutureStream W h k) hτ) ⟨0⟩,
      (if longest then Q.HasLongestSegments else Q.HasShortestSegments) ∧
      ∀ n, boundaryGluingHatEdgeMap W h k hτ (Q.edge n) = P.edge n := by
  obtain ⟨Q, he⟩ := boundaryGluing_infinitePath_lifts_to_hat W h k hτ P
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let z := hatCodes u hτ
  let D := hatLimitExplicitInput u hτ
  let F : Prefunctor (PresentVertex z) (PresentVertex w) := {
    obj := fun a => shiftLimitVertex w t ⟨hatLimitVertexMap u hτ a.id⟩
    map := fun {a b} e => by
      let f : {e : ℕ // EdgePresent u e} :=
        ⟨hatLimitEdgeMap u hτ e.val, (hatLimit_edge_incidence D e.property.1).1⟩
      have hi := shiftLimitEdge_incidence w t f
      have hh := hatLimit_edge_incidence D e.property.1
      exact ⟨shiftLimitEdge w t f, shiftLimitEdge_present w t f,
        hi.1.trans (congrArg (fun v => (shiftLimitVertex w t ⟨v⟩).id)
          (hh.2.1.trans (congrArg (hatLimitVertexMap u hτ) e.property.2.1))),
        hi.2.trans (congrArg (fun v => (shiftLimitVertex w t ⟨v⟩).id)
          (hh.2.2.trans (congrArg (hatLimitVertexMap u hτ) e.property.2.2)))⟩ }
  have hroot : F.obj ⟨0⟩ = boundaryPresentVertex w h k := by
    change shiftLimitVertex w t ⟨hatLimitVertexMap u hτ 0⟩ = _
    rw [D.root, shiftLimitVertex_eq w t 0 ⟨0⟩ (by change 0 < 2; decide)]
    exact congrArg PresentVertex.mk (kmswShift_root_vertex_map w h k)
  obtain ⟨P', he', hv, _, _, _⟩ := rawHat_infinitePath_transport w h k hτ D Q
  have hsame : P' = P :=
    Xdp.LeftmostXdpTransport.infinitePresentPath_eq_of_edge_eq w P P' (by
      funext n
      rw [congrFun he' n]
      exact (boundaryGluingEdgeMap_eq_shift W h k _).symm.trans (he n))
  subst P'
  have hprefix (N : ℕ) :
      if longest then IsLongest (Q.initial N).2 else IsShortest (Q.initial N).2 := by
    have hlen (q : Quiver.Path (⟨0⟩ : PresentVertex z) (Q.initial N).1) :
        ∃ r : Quiver.Path (boundaryPresentVertex w h k) (P.initial N).1,
          r.length = q.length := by
      obtain ⟨r, hr⟩ := boundaryGluing_path_endpoints hroot (hv N).symm (F.mapPath q)
      exact ⟨r, hr.trans (boundaryGluing_mapPath_length F q)⟩
    cases longest with
    | false =>
      intro q
      obtain ⟨r, hr⟩ := hlen q
      have hh := P.initial_isShortest w hP N r
      calc
        (Q.initial N).2.length = N := Q.prefix_length N
        _ = (P.initial N).2.length := (P.prefix_length N).symm
        _ ≤ r.length := hh
        _ = q.length := hr
    | true =>
      intro q
      obtain ⟨r, hr⟩ := hlen q
      have hh := P.initial_isLongest w hP N r
      calc
        q.length = r.length := hr.symm
        _ ≤ (P.initial N).2.length := hh
        _ = N := P.prefix_length N
        _ = (Q.initial N).2.length := (Q.prefix_length N).symm
  have hs : ∀ a b : ℕ, 1 ≤ a → a ≤ b →
      ∃ v, ∃ q : Quiver.Path v (Q.initial b).1,
        q.length = b + 1 - a ∧
        pathEdgeList q = (List.ofFn (fun i : Fin b => Q.edge i.val)).drop (a - 1) ∧
        (if longest then IsLongest q else IsShortest q) := by
    intro a b ha hab
    obtain ⟨v, p, q, hpq, hp⟩ := (Q.initial b).2.exists_eq_comp_of_le_length
      (show a - 1 ≤ (Q.initial b).2.length by rw [Q.prefix_length]; omega)
    refine ⟨v, q, ?_, ?_, ?_⟩
    · have hh := Q.prefix_length b
      rw [hpq, Quiver.Path.length_comp, hp] at hh
      omega
    · rw [← Q.prefix_edges b, hpq, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
      exact List.drop_left.symm
    · have hh := hprefix b
      rw [hpq] at hh
      cases longest with
      | false => exact IsShortest.of_comp_right hh
      | true => exact IsLongest.of_comp_right hh
  exact ⟨Q, by cases longest <;> exact hs, he⟩

/-- Helper toward Lemma 5.5: the leftmost edge-order characterization is
unchanged when the code stream is rewritten by its exact decoding identity. -/
private theorem boundaryGluing_cast_firstDivergence {u v : ℕ → Fin 3}
    (huv : u = v) (longest : Bool) (hf : KMSWFiniteIncidence u)
    (hL : ∀ n, 0 ≤ L u n) (ht : Filter.Tendsto (L u) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R u n ≤ a) (A : InfinitePresentPath u ⟨0⟩)
    (hA : ∀ B : InfinitePresentPath u ⟨0⟩,
      (if longest then B.HasLongestSegments else B.HasShortestSegments) →
      GeodesicFirstDivergenceRightOf u hf hL ht hR 0 A B) :
    ∀ B : InfinitePresentPath v ⟨0⟩,
      (if longest then B.HasLongestSegments else B.HasShortestSegments) →
      GeodesicFirstDivergenceRightOf v (huv ▸ hf) (huv ▸ hL) (huv ▸ ht) (huv ▸ hR)
        0 (huv ▸ A) B := by
  subst v
  exact hA

/-! Edge coverage is independent of the outstanding component labels. -/



private def gluing_prependPath {w : ℕ → Fin 3} {u v : PresentVertex w}
    (e : Quiver.Hom u v) (Q : InfinitePresentPath w v) : InfinitePresentPath w u where
  edge
    | 0 => e.val
    | n + 1 => Q.edge n
  initial
    | 0 => ⟨u, .nil⟩
    | n + 1 => ⟨(Q.initial n).1, e.toPath.comp (Q.initial n).2⟩
  prefix_length n := by
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath,
        Q.prefix_length, Nat.add_comm]
  prefix_edges n := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [pathEdgeList_comp, Q.prefix_edges, List.ofFn_succ]
      rfl



private theorem gluing_extendPath {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Quiver.Path u v) (S : InfinitePresentPath w v) :
    ∃ Q : InfinitePresentPath w u, Set.range S.edge ⊆ Set.range Q.edge := by
  induction p with
  | nil => exact ⟨S, Set.Subset.rfl⟩
  | @cons v z p e ih =>
    obtain ⟨Q, hQ⟩ := ih (gluing_prependPath e S)
    refine ⟨Q, ?_⟩
    rintro f ⟨i, rfl⟩
    exact hQ ⟨i + 1, rfl⟩




private theorem gluing_sideEdges_cover (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (P : InfinitePresentPath w ⟨0⟩) (e : ℕ) :
    e ∈ sideEdges w hfin hL htrans hR P .left ∨
      e ∈ sideEdges w hfin hL htrans hR P .right := by
  classical
  by_cases hs : ∃ i, P.edge i = e
  · obtain ⟨i, rfl⟩ := hs
    exact Or.inl (seamEdge_mem_sideEdges w hfin hL htrans hR P .left i)
  · have hoff : ∀ i, e ≠ P.edge i := fun i hi => hs ⟨i, hi.symm⟩
    obtain ⟨N, hN⟩ := eventually_present_of_nonneg_of_unbounded w hL hR e
    have he : EdgePresent w e := ⟨N, hN N le_rfl⟩
    have hv := (kmswStage_endpoints_lt_nextVertex w N e (hN N le_rfl).1).1
    rw [(edge_endpoints_eq w (hN N le_rfl).1).1] at hv
    obtain ⟨p⟩ := allocated_stage_reachable_from_zero w hL N (edgeWest w e) hv
    let f : Quiver.Hom (⟨edgeWest w e⟩ : PresentVertex w) ⟨edgeEast w e⟩ :=
      ⟨e, he, rfl, rfl⟩
    let S := gluing_prependPath f (kmswRightmostPath w hfin hL htrans hR (edgeEast w e))
    obtain ⟨Q, hQ⟩ := gluing_extendPath p S
    obtain ⟨i, hi⟩ := hQ (show e ∈ Set.range S.edge from ⟨0, rfl⟩)
    have hzQ : thinMapArcSeed w hfin e ∈ pathTrace
        (monotoneFamilyDrawing w hfin (monotone_family_all w))
        (fun j => (Q.edge j, false)) := by
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      dsimp only
      rw [hi]
      exact (thinMapArcSeed_mem_interior w hfin e).1
    have hz := thinMapPathTrace_subset_sideRegions w hfin hL htrans hR P Q hzQ
    rcases hz with hl | hr
    · exact Or.inl ((thinMapArc_subset_sideRegion_iff_seed
        w hfin hL htrans hR P .left e hoff).mpr hl)
    · exact Or.inr ((thinMapArc_subset_sideRegion_iff_seed
        w hfin hL htrans hR P .right e hoff).mpr hr)




theorem boundaryGluingLeftHatEdges_union_rightHatEdges :
    boundaryGluingLeftHatEdges W h k hτ x hq ∪
      boundaryGluingRightHatEdges W h k hτ x hq =
        Set.range (boundaryGluingHatEdgeMap W h k hτ) := by
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  have hcover (e : ℕ) :
      e ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges ∨
      e ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges := by
    change e ∈ (⋃ s, geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime
      .left q s) ∨ e ∈ (⋃ s, geometricAncestorEdges x renewalTime
        renewalTime_positiveSuccessTime .right q s)
    rw [iUnion_geometricAncestorEdges, iUnion_geometricAncestorEdges]
    exact gluing_sideEdges_cover _ _ _ _ _ _ e
  apply Set.Subset.antisymm
  · rintro e (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) <;> exact ⟨a, rfl⟩
  · rintro e ⟨a, rfl⟩
    rcases hcover a with hl | hr
    · exact Or.inl ⟨a, hl, rfl⟩
    · exact Or.inr ⟨a, hr, rfl⟩



theorem boundaryGluing_hatRange_union_primedEdges
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    Set.range (boundaryGluingHatEdgeMap W h k hτ) ∪
      boundaryGluingPrimedEdges W h k hτ = Set.range (boundaryGluingEdgeMap W h k) := by
  let u := boundaryGluingFutureStream W h k
  apply Set.Subset.antisymm
  · rintro e (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨hatLimitEdgeMap u hτ a, rfl⟩
    · exact ⟨primedLimitEdgeMap u hτ a, rfl⟩
  · rintro e ⟨a, rfl⟩
    by_cases ha : MhatGeometricEdge u a
    · obtain ⟨b, rfl⟩ := (hatLimitEdgeMap_geometric_range_iff u hτ a).mpr ha
      exact Or.inl ⟨b, rfl⟩
    · obtain ⟨b, rfl⟩ := (primeGeomEdge_iff_primedLimitEdge u hfin
        (hatBoundaryHitWitnesses u hτ) hτ a).mp (Or.inl ha)
      exact Or.inr ⟨b, rfl⟩



theorem boundaryGluing_prefix_union_futureRange :
    boundaryGluingPrefixEdges W h k ∪ Set.range (boundaryGluingEdgeMap W h k) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  by_cases he : e < (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).nextEdge
  · exact Or.inl he
  · exact Or.inr (kmswWindowEdgeMapInf_range_of_new _ _ e (Nat.le_of_not_gt he))




theorem boundaryGluing_layout_union
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    boundaryGluingPrefixEdges W h k ∪ boundaryGluingLeftHatEdges W h k hτ x hq ∪
      boundaryGluingPrimedEdges W h k hτ ∪
        boundaryGluingRightHatEdges W h k hτ x hq = Set.univ := by
  have hhat := boundaryGluingLeftHatEdges_union_rightHatEdges W h k hτ x hq
  have hfuture := boundaryGluing_hatRange_union_primedEdges W h k hτ hfin
  have hall := boundaryGluing_prefix_union_futureRange W h k
  rw [← hfuture, ← hhat] at hall
  ext e
  simpa only [Set.mem_union, Set.mem_univ, or_assoc, or_left_comm, or_comm] using
    Set.ext_iff.mp hall e



theorem boundaryGluing_nonneg_layout_union
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    boundaryGluingPrefixMinusEdges W h k ∪
      boundaryGluingLeftHatEdges W h k hτ x hq ∪
      boundaryGluingPrimedEdges W h k hτ ∪
        boundaryGluingRightHatEdges W h k hτ x hq = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  have he := Set.eq_univ_iff_forall.mp
    (boundaryGluing_layout_union W h k hτ x hq hfin) e
  rcases he with ((hf | hl) | hp) | hr
  · by_cases ha : e = act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
    · subst e
      exact Or.inr (boundaryGluing_active_mem_rightHatEdges W h k hτ x hq)
    · exact Or.inl (Or.inl (Or.inl ⟨hf, ha⟩))
  · exact Or.inl (Or.inl (Or.inr hl))
  · exact Or.inl (Or.inr hp)
  · exact Or.inr hr

section RemainingObligations

variable {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  (longest : Bool)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)






@[expose] noncomputable def BoundaryGluingGeodesicIdentification
    (P : M0CutInfiniteGeodesic W H h hLL k longest) : Prop :=
  ∀ i : ℕ, P.codePath.edge i = boundaryGluingHatEdgeMap W h k hτ
    ((sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩).edge i)





theorem boundaryGluing_exists_embedded_cutGeodesic :
    ∃ Q : M0CutInfiniteGeodesic W H h hLL k longest,
      BoundaryGluingGeodesicIdentification W h k hτ longest hqMode Q := by
  obtain ⟨P, hP, he⟩ := boundaryGluing_exists_embedded_geodesic W h k hτ longest hqMode
  have hstart : (P.initial 0).1.id = boundaryVertex (shiftedStream W 0) h k := by
    have hz := (P.initial 0).2.eq_of_length_zero (P.prefix_length 0)
    exact congrArg PresentVertex.id hz.symm
  refine ⟨⟨P, hP, ?_, ?_⟩, he⟩
  · exact ((m0CutData W H h hLL).x_eq h hLL k).trans
      (congrArg (wholePlaneVertexι W 0) hstart.symm)
  · intro n
    apply (m0Cut_identification_directedStep W H h hLL
      ((P.initial n).1.id) ((P.initial (n + 1)).1.id)).2
    obtain ⟨hp, hw⟩ := P.edge_outgoing_at_initial (shiftedStream W 0) n
    obtain ⟨_, ht⟩ := P.edge_incoming_at_succ (shiftedStream W 0) n
    exact ⟨P.edge n, hp, congrArg (wholePlaneVertexι W 0) hw,
      congrArg (wholePlaneVertexι W 0) ht⟩





theorem boundaryGluing_geodesicIdentification
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T) :
    BoundaryGluingGeodesicIdentification W h k hτ longest hqMode P := by
  let w := shiftedStream W 0
  let u := boundaryGluingFutureStream W h k
  let z := hatCodes u hτ
  let q : selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime := ⟨boundaryFutureHattedPath k W, hqMode⟩
  let A := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime q
  have hcode := boundaryGluing_decoded_stream W h k hτ
  change boltzmannKMSWStream (pathCode q.val) = z at hcode
  let Ahat : InfinitePresentPath z ⟨0⟩ := hcode ▸ A
  let hf := sourceAncestor_finite_incidence (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime q
  let hL := sourceAncestor_left_nonneg (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime q
  let ht := sourceAncestor_left_transient (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime q
  let hR := sourceAncestor_right_unbounded (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime q
  have hA : ∀ B : InfinitePresentPath (boltzmannKMSWStream (pathCode q.val)) ⟨0⟩,
      (if longest then B.HasLongestSegments else B.HasShortestSegments) →
      GeodesicFirstDivergenceRightOf _ hf hL ht hR 0 A B := by
    cases longest with
    | false => exact kmswLeftmostSdpPath_firstDivergenceRightOf _ _ _ _ _ _ _
    | true => exact kmswLeftmostLdpPath_firstDivergenceRightOf _ _ _ _ _ _ _
  have hAhat := boundaryGluing_cast_firstDivergence hcode longest hf hL ht hR A hA
  have hLhat : ∀ n, 0 ≤ L z n := hcode ▸ hL
  have hthat : Filter.Tendsto (L z) Filter.atTop Filter.atTop := hcode ▸ ht
  have hRhat : ∀ a : ℤ, ∃ n, R z n ≤ a := hcode ▸ hR
  have hedge (n : ℕ) : Ahat.edge n = A.edge n := by
    have hcast {v v' : ℕ → Fin 3} (heq : v = v')
        (B : InfinitePresentPath v ⟨0⟩) : (heq ▸ B).edge n = B.edge n := by
      subst v'
      rfl
    exact hcast hcode A
  obtain ⟨Q, hQ⟩ := boundaryGluing_exists_embedded_cutGeodesic
    W h k hτ longest hqMode (H := H) (hLL := hLL)
  have heQ (n : ℕ) : Q.codePath.edge n = boundaryGluingHatEdgeMap W h k hτ (Ahat.edge n) :=
    (hQ n).trans (congrArg (boundaryGluingHatEdgeMap W h k hτ) (hedge n).symm)
  obtain ⟨S, hS, heS⟩ := boundaryGluing_infiniteGeodesic_lifts_to_hat
    W h k hτ longest P.codePath P.segments
  let G := monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)
  let hfam : ∀ n, ∃ B : StageDrawing w n, Nonempty (MonotoneStageInvariant w n B) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  have hcontain : pathTrace G (fun n => (Q.codePath.edge n, false)) ⊆
      closedBetween (pathTrace G (fun n => (P.codePath.edge n, false)))
        (pathTrace G (fun n => (T.edge n, false))) := by
    cases longest with
    | false =>
      exact (Xdp.Sdp.cutLeftmost_iff_runZero W H h hp hLL k P T).mp hleft
        Q.codePath Q.segments
    | true =>
      exact (Xdp.cutLeftmost_iff_runZero W H h hp hLL k P T).mp hleft
        Q.codePath Q.segments
  have hang := ((Xdp.LeftmostXdpTransport.trace_subset_closedBetween_iff_departureArgs
    w (H.1 0) hfam (boundaryVertex w h k) P.codePath T Q.codePath).mp hcontain).1
  have hequal : P.codePath.edge = Q.codePath.edge := by
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hpfx : List.ofFn (fun i : Fin n => P.codePath.edge i.val) =
          List.ofFn (fun i : Fin n => Q.codePath.edge i.val) := by
        apply congrArg List.ofFn
        funext i
        exact ih i.val i.isLt
      have hv := P.codePath.initial_vertex_eq_of_prefix_eq Q.codePath n hpfx
      have hpfxHat (i : ℕ) (hi : i < n) : Ahat.edge i = S.edge i := by
        apply boundaryGluingHatEdgeMap_injective W h k hτ
        exact (heQ i).symm.trans ((ih i hi).symm.trans (heS i).symm)
      have hidx := hAhat S hS n hpfxHat
      have hprefix : List.ofFn (fun i : Fin n => Ahat.edge i.val) =
          List.ofFn (fun i : Fin n => S.edge i.val) := by
        apply congrArg List.ofFn
        funext i
        exact hpfxHat i.val i.isLt
      have houtA := Ahat.edge_outgoing n
      have houtS := S.edge_outgoing n
      rw [← hprefix] at houtS
      have harg := boundaryGluing_outgoing_index_arg_le W h k hτ (H.1 0) hfin
        hLhat hthat hRhat (geodesicPrefixEnd z 0
          (List.ofFn (fun i : Fin n => Ahat.edge i.val)))
        (Ahat.edge n) (S.edge n) houtA houtS hidx
      change Complex.arg (G.arc (boundaryGluingHatEdgeMap W h k hτ (S.edge n), false)
          ).initialDirection ≤
        Complex.arg (G.arc (boundaryGluingHatEdgeMap W h k hτ (Ahat.edge n), false)
          ).initialDirection at harg
      rw [heS n, ← heQ n] at harg
      have hvD : kmswLimitDartVertex w (P.codePath.edge n, false) =
          kmswLimitDartVertex w (Q.codePath.edge n, false) :=
        (P.codePath.edge_outgoing_at_initial w n).2.trans
          ((congrArg PresentVertex.id hv).trans (Q.codePath.edge_outgoing_at_initial w n).2.symm)
      exact congrArg Prod.fst (G.initial_arg_injective _ _ hvD
        (le_antisymm harg (hang n n hv)))
  intro n
  exact (congrFun hequal n).trans (hQ n)






@[expose] noncomputable def BoundaryGluingGeodesicIdentificationGoal
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : ∀ j : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h j))
    (P : ∀ j : ℤ, M0CutInfiniteGeodesic W H h hLL j longest) : Prop :=
  (∀ j n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
    ((T j).initial n).1.id ((T j).edge n)) →
  (∀ j, Xdp.CutLeftmostXdp W H h hp hLL longest j (P j) (T j)) →
  ∀ (k : ℤ) (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)),
    hatRootedMapClause (boundaryGluingFutureStream W h k) hτ hfin →
    ∀ hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
        (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime,
      BoundaryGluingGeodesicIdentification W h k hτ longest hqMode (P k)



theorem boundaryGluing_geodesicIdentificationGoal
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : ∀ j : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h j))
    (P : ∀ j : ℤ, M0CutInfiniteGeodesic W H h hLL j longest) :
    BoundaryGluingGeodesicIdentificationGoal W h longest hp T P := by
  intro _hT hleft j hτ hfin _hmap hq
  exact boundaryGluing_geodesicIdentification W h j hτ longest hq hp (T j) (P j)
    hfin (hleft j)






@[expose] noncomputable def BoundaryGluingSideIdentities
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) : Prop :=
  (0 ≤ k →
    (m0GeodesicSide hp P .right).edges =
      boundaryGluingRightHatEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode ∧
    (m0GeodesicSide hp P .left).edges =
      boundaryGluingPrefixMinusEdges W h k ∪
        boundaryGluingLeftHatEdges W h k hτ
          (if longest then XDP.ldp else XDP.sdp) hqMode ∪
        boundaryGluingPrimedEdges W h k hτ) ∧
  (k ≤ 0 →
    (m0GeodesicSide hp P .left).edges =
      boundaryGluingPrimedEdges W h k hτ ∪
        boundaryGluingLeftHatEdges W h k hτ
          (if longest then XDP.ldp else XDP.sdp) hqMode ∧
    (m0GeodesicSide hp P .right).edges =
      boundaryGluingPrefixEdges W h k ∪
        boundaryGluingRightHatEdges W h k hτ
          (if longest then XDP.ldp else XDP.sdp) hqMode)





theorem boundaryGluing_m0SideEdges_inter
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    (m0GeodesicSide hp P .left).edges ∩
      (m0GeodesicSide hp P .right).edges = m0GeodesicEdges P := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  apply Set.Subset.antisymm
  · rintro e ⟨hl, hr⟩
    classical
    by_contra he
    obtain ⟨z, hz⟩ := gluing_arc_interior_nonempty G (wholePlaneDartι W 0 (e, false))
    have hzP : z ∈ m0GeodesicTrace hp P := by
      rw [← m0GeodesicSideRegion_inter hp P]
      exact ⟨hl hz.1, hr hz.1⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzP
    have hne (b : Bool) : wholePlaneDartι W 0 (m0GeodesicSeam P i) ≠
        wholePlaneDartι W 0 (e, b) := by
      intro hh
      exact he ⟨i, wholePlaneEdgeι_injective W 0 (congrArg Prod.fst hh)⟩
    have hnotStart : z ≠ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).start := by
      intro hh
      exact G.interior_avoids_vertices (wholePlaneDartι W 0 (e, false)) _
        ((hh.trans (G.arc_start _)) ▸ hz)
    have hnotFinish : z ≠ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).finish := by
      intro hh
      exact G.interior_avoids_vertices (wholePlaneDartι W 0 (e, false)) _
        ((hh.trans (G.arc_finish _)) ▸ hz)
    have hiz : z ∈ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).interior :=
      ⟨hi, by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
        And.intro hnotStart hnotFinish⟩
    exact Set.disjoint_left.mp
      (G.interior_disjoint (wholePlaneDartι W 0 (e, false))
        (wholePlaneDartι W 0 (m0GeodesicSeam P i)) (hne false) (hne true)) hz hiz
  · exact m0GeodesicEdges_subset_both hp P





theorem boundaryGluing_m0GeodesicEdges_eq_hatSeam
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T) :
    m0GeodesicEdges P = boundaryGluingHatSeamEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode := by
  have he := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp T P hfin hleft
  apply Set.Subset.antisymm
  · rintro e ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, (he i).symm⟩
  · rintro e ⟨a, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, he i⟩




theorem boundaryGluing_m0SideEdges_inter_eq_hatSeam
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T) :
    (m0GeodesicSide hp P .left).edges ∩ (m0GeodesicSide hp P .right).edges =
      boundaryGluingHatSeamEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode := by
  rw [boundaryGluing_m0SideEdges_inter W h k longest hp P]
  exact boundaryGluing_m0GeodesicEdges_eq_hatSeam W h k hτ longest hqMode
    hp T P hfin hleft




theorem boundaryGluing_m0SideEdges_exactly_one_off_hatSeam
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T)
    (e : ℕ) (he : e ∉ boundaryGluingHatSeamEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode) :
    (e ∈ (m0GeodesicSide hp P .left).edges ∧
      e ∉ (m0GeodesicSide hp P .right).edges) ∨
    (e ∈ (m0GeodesicSide hp P .right).edges ∧
      e ∉ (m0GeodesicSide hp P .left).edges) := by
  have hnot : ¬ (e ∈ (m0GeodesicSide hp P .left).edges ∧
      e ∈ (m0GeodesicSide hp P .right).edges) := by
    intro hh
    apply he
    rw [← boundaryGluing_m0SideEdges_inter_eq_hatSeam W h k hτ longest hqMode
      hp T P hfin hleft]
    exact hh
  rcases m0GeodesicSideEdges_cover hp P e with hl | hr
  · exact Or.inl ⟨hl, fun hr => hnot ⟨hl, hr⟩⟩
  · exact Or.inr ⟨hr, fun hl => hnot ⟨hl, hr⟩⟩




theorem boundaryGluing_nonneg_layout_inter (hk : 0 ≤ k)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    (boundaryGluingPrefixMinusEdges W h k ∪ boundaryGluingLeftHatEdges W h k hτ x hq ∪
      boundaryGluingPrimedEdges W h k hτ) ∩ boundaryGluingRightHatEdges W h k hτ x hq =
        boundaryGluingHatSeamEdges W h k hτ x hq := by
  apply Set.Subset.antisymm
  · rintro e ⟨(hf | hl) | hp, hr⟩
    · have hh : e ∈ boundaryGluingPrefixMinusEdges W h k ∩
          boundaryGluingHatSideEdges W h k hτ x hq .right := ⟨hf, hr⟩
      rw [boundaryGluingPrefixMinusEdges_inter_hatSideEdges W h k hτ x hq hk .right] at hh
      exact hh.elim
    · rw [← boundaryGluingLeftHatEdges_inter_rightHatEdges W h k hτ x hq]
      exact ⟨hl, hr⟩
    · have hh : e ∈ boundaryGluingPrimedEdges W h k hτ ∩
          boundaryGluingRightHatEdges W h k hτ x hq := ⟨hp, hr⟩
      rw [boundaryGluingPrimedEdges_inter_rightHatEdges W h k hτ x hq hfin] at hh
      exact hh.2
  · intro e he
    have hh := boundaryGluingHatSeamEdges_subset_both W h k hτ x hq he
    exact ⟨Or.inl (Or.inr hh.1), hh.2⟩

/-! The local component transport below proves the non-crossing part of T0.
It does not assign a component to either embedded hatted side. -/



theorem boundaryGluingUpperLeftEdges_of_nonpos (hk : k ≤ 0) :
    boundaryGluingUpperLeftEdges W h k = ∅ := by
  have hUL : (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).UL =
        [act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)] := by
    by_cases hk0 : k = 0
    · subst k
      rw [boundaryHitTime_zero]
      rfl
    · exact (leftHit_UL_singleton_and_west_endpoint _ h (by omega)).1
  simp only [boundaryGluingUpperLeftEdges, hUL, List.dropLast_singleton,
    List.not_mem_nil, Set.ofPred_false]




theorem boundaryGluing_nonpos_layout_inter (hk : k ≤ 0)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    (boundaryGluingPrimedEdges W h k hτ ∪
      boundaryGluingLeftHatEdges W h k hτ x hq) ∩
      (boundaryGluingPrefixEdges W h k ∪
        boundaryGluingRightHatEdges W h k hτ x hq) =
          boundaryGluingHatSeamEdges W h k hτ x hq := by
  apply Set.Subset.antisymm
  · rintro e ⟨hp | hl, hf | hr⟩
    · have he : e ∈ boundaryGluingPrefixEdges W h k ∩
          boundaryGluingPrimedEdges W h k hτ := ⟨hf, hp⟩
      rw [boundaryGluingPrefixEdges_inter_primedEdges_eq_upperLeft_union_beta
        W h k hτ x hq hfin, boundaryGluingUpperLeftEdges_of_nonpos W h k hk,
        Set.empty_union] at he
      rw [← boundaryGluingLeftHatEdges_inter_rightHatEdges W h k hτ x hq]
      exact ⟨boundaryGluingBetaEdges_subset_leftHatEdges W h k hτ x hq he.2,
        boundaryGluingUpperRightEdges_subset_rightHatEdges W h k hτ x hq hfin he.1⟩
    · have he : e ∈ boundaryGluingPrimedEdges W h k hτ ∩
          boundaryGluingRightHatEdges W h k hτ x hq := ⟨hp, hr⟩
      rw [boundaryGluingPrimedEdges_inter_rightHatEdges W h k hτ x hq hfin] at he
      exact he.2
    · have he : e ∈ boundaryGluingPrefixEdges W h k ∩
          boundaryGluingLeftHatEdges W h k hτ x hq := ⟨hf, hl⟩
      rw [boundaryGluingPrefixEdges_inter_leftHatEdges_eq_upperRight_inter_seam
        W h k hτ x hq hfin] at he
      exact he.2
    · rw [← boundaryGluingLeftHatEdges_inter_rightHatEdges W h k hτ x hq]
      exact ⟨hl, hr⟩
  · intro e he
    have hs := boundaryGluingHatSeamEdges_subset_both W h k hτ x hq he
    exact ⟨Or.inr hs.1, Or.inr hs.2⟩




theorem boundaryGluing_edge_partitions
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    (0 ≤ k →
      (boundaryGluingPrefixMinusEdges W h k ∪
        boundaryGluingLeftHatEdges W h k hτ x hq ∪
        boundaryGluingPrimedEdges W h k hτ) ∪
          boundaryGluingRightHatEdges W h k hτ x hq = Set.univ ∧
      (boundaryGluingPrefixMinusEdges W h k ∪
        boundaryGluingLeftHatEdges W h k hτ x hq ∪
        boundaryGluingPrimedEdges W h k hτ) ∩
          boundaryGluingRightHatEdges W h k hτ x hq =
            boundaryGluingHatSeamEdges W h k hτ x hq) ∧
    (k ≤ 0 →
      (boundaryGluingPrimedEdges W h k hτ ∪
        boundaryGluingLeftHatEdges W h k hτ x hq) ∪
        (boundaryGluingPrefixEdges W h k ∪
          boundaryGluingRightHatEdges W h k hτ x hq) = Set.univ ∧
      (boundaryGluingPrimedEdges W h k hτ ∪
        boundaryGluingLeftHatEdges W h k hτ x hq) ∩
        (boundaryGluingPrefixEdges W h k ∪
          boundaryGluingRightHatEdges W h k hτ x hq) =
            boundaryGluingHatSeamEdges W h k hτ x hq) := by
  constructor
  · intro hk
    exact ⟨boundaryGluing_nonneg_layout_union W h k hτ x hq hfin,
      boundaryGluing_nonneg_layout_inter W h k hτ x hq hk hfin⟩
  · intro hk
    refine ⟨?_, boundaryGluing_nonpos_layout_inter W h k hτ x hq hk hfin⟩
    have hall := boundaryGluing_layout_union W h k hτ x hq hfin
    ext e
    simpa only [Set.mem_union, Set.mem_univ, or_assoc, or_left_comm, or_comm] using
      Set.ext_iff.mp hall e




theorem boundaryGluing_arc_interior_disjoint_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) :
    Disjoint ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior (m0GeodesicTrace hp P) := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  apply Set.disjoint_left.mpr
  intro z hz hzP
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzP
  have hne (b : Bool) : wholePlaneDartι W 0 (m0GeodesicSeam P i) ≠
      wholePlaneDartι W 0 (e, b) := by
    intro hh
    exact he ⟨i, wholePlaneEdgeι_injective W 0 (congrArg Prod.fst hh)⟩
  have hnotStart : z ≠ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).start := by
    intro hh
    exact G.interior_avoids_vertices (wholePlaneDartι W 0 (e, false)) _
      ((hh.trans (G.arc_start _)) ▸ hz)
  have hnotFinish : z ≠ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).finish := by
    intro hh
    exact G.interior_avoids_vertices (wholePlaneDartι W 0 (e, false)) _
      ((hh.trans (G.arc_finish _)) ▸ hz)
  have hiz : z ∈ (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).interior :=
    ⟨hi, by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
      And.intro hnotStart hnotFinish⟩
  exact Set.disjoint_left.mp
    (G.interior_disjoint (wholePlaneDartι W 0 (e, false))
      (wholePlaneDartι W 0 (m0GeodesicSeam P i)) (hne false) (hne true)) hz hiz




theorem boundaryGluing_sideEdges_iff_interiorPoint
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) {z : ℂ}
    (hz : z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior) :
    (e ∈ (m0GeodesicSide hp P .left).edges ↔ z ∈ m0GeodesicLeftOpen hp P) ∧
      (e ∈ (m0GeodesicSide hp P .right).edges ↔ z ∉ m0GeodesicLeftOpen hp P) := by
  have hznot : z ∉ m0GeodesicTrace hp P := fun hzP =>
    Set.disjoint_left.mp
      (boundaryGluing_arc_interior_disjoint_trace W h k longest hp P he) hz hzP
  have hzR := m0Geodesic_arc_subset_ambient hp e hz.1
  constructor
  · constructor
    · intro hl
      exact m0GeodesicLeftOpen_closure_inter_complement_subset hp P
        ⟨(hl hz.1).1, hzR, hznot⟩
    · intro hzL
      rcases m0GeodesicSideEdges_cover hp P e with hl | hr
      · exact hl
      · exact ((hr hz.1).2 hzL).elim
  · constructor
    · intro hr
      exact (hr hz.1).2
    · intro hzL
      rcases m0GeodesicSideEdges_cover hp P e with hl | hr
      · exact (hzL (m0GeodesicLeftOpen_closure_inter_complement_subset hp P
          ⟨(hl hz.1).1, hzR, hznot⟩)).elim
      · exact hr




theorem boundaryGluing_off_hatSeam_arc_interior_subset_complement
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T) {e : ℕ}
    (he : e ∉ boundaryGluingHatSeamEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior ⊆
        m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
  have heP : e ∉ m0GeodesicEdges P := by
    rw [boundaryGluing_m0GeodesicEdges_eq_hatSeam W h k hτ longest hqMode
      hp T P hfin hleft]
    exact he
  intro z hz
  exact ⟨m0Geodesic_arc_subset_ambient hp e hz.1,
    fun hzP => Set.disjoint_left.mp
      (boundaryGluing_arc_interior_disjoint_trace W h k longest hp P heP) hz hzP⟩



private theorem gluing_polyline_height_on_image {p : Polyline} (hp : p.XMonotone)
    {z : ℂ} (hz : z ∈ p.image) : z.im = p.heightFn z.re := by
  rcases hz with rfl | ⟨i, hi, hz⟩
  · have hh := p.heightFn_point hp (show 0 < p.points.length from
      List.length_pos_iff.mpr p.nonempty)
    rw [p.point_zero_eq_start] at hh
    exact hh.symm
  · have hlt := p.point_re_lt hp (Nat.lt_succ_self i) hi
    have hm := (mem_segment_iff_height hlt).mp hz
    have hh := p.heightFn_linear_on_segment hp hi hm.1 hm.2.1
    exact hm.2.2.trans hh.symm



private theorem gluing_runZero_arc_graph
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (e : ℕ) :
    let p := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))
    p.image = graphOver p.start.re p.finish.re p.heightFn ∧ p.XMonotone := by
  let w := shiftedStream W 0
  have he := kmsw_edge_allocated_by_self w e
  have harc : (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false)) = layoutArc w e e := by
    apply (WholePlanePastGlueData.gluedArc_runZero W h hp H (e, false)).trans
    exact monotoneLimitDrawing_arc_layout w (H.1 0) _ e e he false
  dsimp only
  rw [harc]
  let p := layoutArc w e e
  have hm : p.XMonotone := layoutArc_points_pairwise w e e he
  refine ⟨?_, hm⟩
  obtain ⟨f, hf⟩ := layoutArc_image_graph w e e he
  have hg : p.image = graphOver p.start.re p.finish.re f := by
    change p.image = {z | p.start.re ≤ z.re ∧ z.re ≤ p.finish.re ∧ z.im = f z.re}
    rw [show p.start = layoutPos w e ((kmswStage w e).west e) from
      (layoutArc_endpoints w e e he).1,
      show p.finish = layoutPos w e ((kmswStage w e).east e) from
      (layoutArc_endpoints w e e he).2]
    exact hf
  ext z
  constructor
  · intro hz
    have hb : z ∈ graphOver p.start.re p.finish.re f := hg ▸ hz
    exact ⟨hb.1, hb.2.1, gluing_polyline_height_on_image hm hz⟩
  · intro hz
    have hq : (⟨z.re, f z.re⟩ : ℂ) ∈ p.image := by
      rw [hg]
      exact ⟨hz.1, hz.2.1, rfl⟩
    have hh := gluing_polyline_height_on_image hm hq
    have hqz : (⟨z.re, f z.re⟩ : ℂ) = z := Complex.ext rfl (hh.trans hz.2.2.symm)
    exact hqz ▸ hq



private theorem gluing_polyline_interior_connected_dense {p : Polyline}
    (hm : p.XMonotone) (hlen : 2 ≤ p.points.length)
    (hg : p.image = graphOver p.start.re p.finish.re p.heightFn) :
    IsPreconnected p.interior ∧ p.image ⊆ closure p.interior := by
  have hab : p.start.re < p.finish.re := by
    rw [← p.point_zero_eq_start, ← p.point_last_eq_finish]
    exact p.point_re_lt hm (by omega) (by omega)
  have hstart : graphParam p.heightFn p.start.re = p.start := by
    apply Complex.ext
    · simp [graphParam]
    · simpa [graphParam] using (gluing_polyline_height_on_image hm (Or.inl rfl)).symm
  have hfinish : graphParam p.heightFn p.finish.re = p.finish := by
    have hh := p.heightFn_point hm (show p.points.length - 1 < p.points.length by omega)
    rw [p.point_last_eq_finish] at hh
    apply Complex.ext
    · simp [graphParam]
    · simpa [graphParam] using hh
  have hi : p.interior = graphParam p.heightFn '' Set.Ioo p.start.re p.finish.re := by
    ext z
    constructor
    · rintro ⟨hz, hne⟩
      rw [hg, graphOver_eq_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxa : x ≠ p.start.re := by
        intro heq
        exact hne (by simp [heq, hstart])
      have hxb : x ≠ p.finish.re := by
        intro heq
        exact hne (by simp [heq, hfinish])
      exact ⟨x, ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hg, graphOver_eq_image]
        exact ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
      · intro hn
        rcases hn with hn | hn
        · have heq := congrArg Complex.re hn
          simp only [graphParam, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, sub_self, add_zero] at heq
          exact (ne_of_gt hx.1) heq
        · have heq := congrArg Complex.re hn
          simp only [graphParam, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, sub_self, add_zero] at heq
          exact (ne_of_lt hx.2) heq
  have hc : Continuous (graphParam p.heightFn) := by
    unfold graphParam
    have := p.continuous_heightFn
    fun_prop
  refine ⟨?_, ?_⟩
  · rw [hi]
    exact isPreconnected_Ioo.image _ hc.continuousOn
  · rw [hg, graphOver_eq_image, hi, ← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image hc




theorem boundaryGluing_arc_interior_connected_dense
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (e : ℕ) :
    let p := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))
    IsConnected p.interior ∧ p.image ⊆ closure p.interior := by
  obtain ⟨hg, hm⟩ := gluing_runZero_arc_graph W h (H := H) hp e
  have hlen := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc_length
    (wholePlaneDartι W 0 (e, false))
  obtain ⟨hc, hd⟩ := gluing_polyline_interior_connected_dense hm hlen hg
  exact ⟨⟨gluing_arc_interior_nonempty _ _, hc⟩, hd⟩




theorem boundaryGluing_arc_interior_subset_component
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) {z : ℂ}
    (hz : z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior) :
    let p := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))
    let C := connectedComponentIn
      (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z
    p.interior ⊆ C ∧ p.image ⊆ closure C := by
  obtain ⟨hc, hd⟩ := boundaryGluing_arc_interior_connected_dense W h (H := H) hp e
  have hsub : ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior ⊆
        m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
    intro q hq
    exact ⟨m0Geodesic_arc_subset_ambient hp e hq.1, fun hqP =>
      Set.disjoint_left.mp
        (boundaryGluing_arc_interior_disjoint_trace W h k longest hp P he) hq hqP⟩
  have hcomp := hc.isPreconnected.subset_connectedComponentIn hz hsub
  exact ⟨hcomp, hd.trans (closure_mono hcomp)⟩




theorem boundaryGluing_arc_off_trace_subset_component
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) {z : ℂ}
    (hz : z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).image \ m0GeodesicTrace hp P ⊆
        connectedComponentIn
          (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z := by
  let p := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
    (wholePlaneDartι W 0 (e, false))
  obtain ⟨hc, hd⟩ := boundaryGluing_arc_interior_connected_dense W h (H := H) hp e
  intro q hq
  have hconn : IsPreconnected (insert q p.interior) :=
    hc.isPreconnected.subset_closure (Set.subset_insert _ _)
      (Set.insert_subset (hd hq.1) subset_closure)
  have hsub : insert q p.interior ⊆
      m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
    apply Set.insert_subset
    · exact ⟨m0Geodesic_arc_subset_ambient hp e hq.1, hq.2⟩
    · intro u hu
      exact ⟨m0Geodesic_arc_subset_ambient hp e hu.1, fun huP =>
        Set.disjoint_left.mp
          (boundaryGluing_arc_interior_disjoint_trace W h k longest hp P he) hu huP⟩
  exact hconn.subset_connectedComponentIn (Set.mem_insert_of_mem q hz) hsub
    (Set.mem_insert q p.interior)





theorem boundaryGluing_rightHatOffSeam_drawing_subset_complement
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
    let HR := boundaryGluingRightHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode
    let S := boundaryGluingHatSeamEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode
    let V := {v | ∃ e ∈ HR,
      edgeWest (shiftedStream W 0) e = v ∨ edgeEast (shiftedStream W 0) e = v}
    (⋃ e ∈ HR \ S, (G.arc (wholePlaneDartι W 0 (e, false))).interior) ∪
      (fun v => G.pos (wholePlaneVertexι W 0 v)) '' (V \ m0GeodesicVertices P) ⊆
        m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
  dsimp only
  rintro z (hz | hz)
  · obtain ⟨e, he, hz⟩ := Set.mem_iUnion₂.mp hz
    exact boundaryGluing_off_hatSeam_arc_interior_subset_complement W h k hτ
      longest hqMode hp T P hfin hleft he.2 hz
  · obtain ⟨v, hv, rfl⟩ := hz
    exact ⟨m0Geodesic_pos_mem_ambient hp v,
      fun hzP => hv.2 ((m0Geodesic_pos_mem_trace_iff hp P v).mp hzP)⟩





theorem boundaryGluing_off_hatSeam_arc_component
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P T) {e : ℕ}
    (he : e ∉ boundaryGluingHatSeamEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode) :
    let p := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))
    IsConnected p.interior ∧ ∀ z ∈ p.interior,
      p.interior ⊆ connectedComponentIn
        (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z ∧
      p.image \ m0GeodesicTrace hp P ⊆ connectedComponentIn
        (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z := by
  have heP : e ∉ m0GeodesicEdges P := by
    rw [boundaryGluing_m0GeodesicEdges_eq_hatSeam W h k hτ longest hqMode
      hp T P hfin hleft]
    exact he
  refine ⟨(boundaryGluing_arc_interior_connected_dense W h (H := H) hp e).1, ?_⟩
  intro z hz
  exact ⟨(boundaryGluing_arc_interior_subset_component W h k longest hp P heP hz).1,
    boundaryGluing_arc_off_trace_subset_component W h k longest hp P heP hz⟩

/-- the geometric boundary edge immediately west of x_k belongs exclusively to
the literal left side. The result includes a missing west boundary edge and
labels its whole interior by transport from x_{k-1}, not by an assumption. -/
theorem boundaryGluing_previous_boundary_edge_left
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    let e := boundaryOuterEdge (shiftedStream W 0) h (k - 1)
    e ∈ (m0GeodesicSide hp P .left).edges ∧
      e ∉ (m0GeodesicSide hp P .right).edges ∧
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (e, false))).interior ⊆
          m0GeodesicLeftOpen hp P := by
  let e := boundaryOuterEdge (shiftedStream W 0) h (k - 1)
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let b := G.pos ((m0CutData W H h hLL).x (k - 1))
  have he : e ∉ m0GeodesicEdges P := by
    rintro ⟨i, hi⟩
    apply m0Geodesic_previous_not_mem_vertices hp P
    refine ⟨i, ?_⟩
    exact (P.codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2.symm.trans
      ((congrArg (edgeWest (shiftedStream W 0)) hi).trans
        (boundaryOuterEdge_endpoints (shiftedStream W 0) h (k - 1)).1)
  have hs : (G.arc (wholePlaneDartι W 0 (e, false))).start = b := by
    apply (G.arc_start (wholePlaneDartι W 0 (e, false))).trans
    change G.pos (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) e)) = b
    rw [(boundaryOuterEdge_endpoints (shiftedStream W 0) h (k - 1)).1]
    exact congrArg G.pos ((m0CutData W H h hLL).x_eq h hLL (k - 1)).symm
  obtain ⟨z, hz⟩ := gluing_arc_interior_nonempty G (wholePlaneDartι W 0 (e, false))
  have hb : b ∈ connectedComponentIn
      (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z := by
    apply boundaryGluing_arc_off_trace_subset_component W h k longest hp P he hz
    exact ⟨hs ▸ (Or.inl rfl), m0Geodesic_previous_pos_not_mem_trace hp P⟩
  have hc : connectedComponentIn
      (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z =
        m0GeodesicLeftOpen hp P := connectedComponentIn_eq hb
  obtain ⟨hi, hd⟩ := boundaryGluing_arc_interior_subset_component
    W h k longest hp P he hz
  rw [hc] at hi hd
  have hl : e ∈ (m0GeodesicSide hp P .left).edges :=
    fun q hq => ⟨hd hq, m0Geodesic_arc_subset_ambient hp e hq⟩
  refine ⟨hl, ?_, hi⟩
  intro hr
  apply he
  rw [← boundaryGluing_m0SideEdges_inter W h k longest hp P]
  exact ⟨hl, hr⟩

/-- Helper toward Lemma 5.5: a bordering wedge accumulates on the arc interior. -/
private theorem gluing_exists_small_interior_point (p : Polyline) (hlen : 2 ≤ p.points.length)
    (hne : p.initialDirection ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ p.start + t • p.initialDirection ∈ p.interior := by
  let q : ℝ → ℂ := fun t => p.start + t • p.initialDirection
  have hp0 : p.point 0 = p.start := by
    cases p with
    | mk points hpoints =>
      cases points with
      | nil => exact False.elim (hpoints rfl)
      | cons a rest => rfl
  have hline (t : ℝ) : q t = AffineMap.lineMap p.start (p.point 1) t := by
    rw [AffineMap.lineMap_apply_module']
    dsimp [q]
    simp only [Polyline.initialDirection]
    abel
  have hseg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : q t ∈ p.segmentAt 0 := by
    change q t ∈ segment ℝ (p.point 0) (p.point 1)
    rw [hp0, hline]
    exact lineMap_mem_segment ℝ p.start (p.point 1) ⟨ht0, ht1⟩
  have himage (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : q t ∈ p.image := by
    change q t ∈ {p.start} ∪ {z | ∃ i, i + 1 < p.points.length ∧
      z ∈ p.segmentAt i}
    right
    exact ⟨0, by omega, hseg t ht0 ht1⟩
  have hneStart (t : ℝ) (ht : 0 < t) : q t ≠ p.start := by
    intro h
    have hmul : (t : ℂ) * p.initialDirection = 0 := by
      dsimp [q] at h
      have h' : p.start + (t : ℂ) * p.initialDirection = p.start + 0 := by
        simpa using h
      exact add_left_cancel h'
    have htne : t ≠ 0 := ne_of_gt ht
    have hct : (t : ℂ) ≠ 0 := by exact_mod_cast htne
    exact (mul_ne_zero hct hne) hmul
  let m := min δ 1
  have hm : 0 < m := lt_min hδ zero_lt_one
  let a := m / 2
  let b := m / 4
  have ha : 0 < a ∧ a < δ ∧ a < 1 := by
    dsimp [a, m]
    constructor
    · exact half_pos hm
    constructor
    · exact (half_lt_self hm).trans_le (min_le_left _ _)
    · exact (half_lt_self hm).trans_le (min_le_right _ _)
  have hb : 0 < b ∧ b < δ ∧ b < 1 := by
    dsimp [b, m]
    constructor
    · positivity
    constructor
    · have hlt : min δ 1 / 4 < min δ 1 / 2 := by nlinarith [hm]
      exact hlt.trans ha.2.1
    · have hlt : min δ 1 / 4 < min δ 1 / 2 := by nlinarith [hm]
      exact hlt.trans ha.2.2
  have hab : q a ≠ q b := by
    intro h
    have hmul : (a : ℂ) * p.initialDirection = (b : ℂ) * p.initialDirection := by
      have h' := congrArg (fun z : ℂ => z - p.start) h
      dsimp [q] at h'
      simpa only [add_sub_cancel_left] using h'
    have hneab : a - b ≠ 0 := by
      dsimp [a, b]
      nlinarith [hm]
    have hcast : (a : ℂ) = b := mul_right_cancel₀ hne hmul
    have hab' : a = b := by exact_mod_cast hcast
    exact hneab (sub_eq_zero.mpr hab')
  by_cases hfinish : q a = p.finish
  · refine ⟨b, hb.1, hb.2.1, ?_⟩
    rw [Polyline.interior, Set.mem_sdiff]
    refine ⟨himage b (le_of_lt hb.1) (le_of_lt hb.2.2), ?_⟩
    intro h
    rcases Set.mem_insert_iff.mp h with hs | hf
    · exact (hneStart b hb.1) hs
    · exact hab (hfinish.trans hf.symm)
  · refine ⟨a, ha.1, ha.2.1, ?_⟩
    rw [Polyline.interior, Set.mem_sdiff]
    refine ⟨himage a (le_of_lt ha.1) (le_of_lt ha.2.2), ?_⟩
    intro h
    rcases Set.mem_insert_iff.mp h with hs | hf
    · exact (hneStart a ha.1) hs
    · exact hfinish hf

/-- Helper toward Lemma 5.5 (`lem-quad-kmsw`); not a paper result.
If a dart borders a face, the closure of that face meets the arc interior. -/
private theorem gluing_dartBorders_arcInterior_closure {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hF : P.dartBorders d F) :
    ((P.arc d).interior ∩ closure F.val).Nonempty := by
  obtain ⟨δ, hδ, hw⟩ := hF
  obtain ⟨t, ht, htδ, hinterior⟩ :=
    gluing_exists_small_interior_point (P.arc d) (P.arc_length d) (P.initial_nonzero d) hδ
  let g : ℝ → ℂ := fun ε => (P.arc d).start + (t : ℂ) *
    ((P.arc d).initialDirection + (ε : ℂ) * Complex.I * (P.arc d).initialDirection)
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo 0 δ) := by
    rw [closure_Ioo (ne_of_lt hδ)]
    exact ⟨le_rfl, hδ.le⟩
  have hsub : g '' Set.Ioo 0 δ ⊆ F.val := by
    rintro z ⟨ε, hε, rfl⟩
    exact hw t ε ht htδ hε.1 hε.2
  have hz := closure_mono hsub (mem_closure_image hg.continuousAt hzero)
  have hz' : (P.arc d).start + (t : ℂ) * (P.arc d).initialDirection ∈ closure F.val := by
    simpa [g] using hz
  exact ⟨(P.arc d).start + (t : ℂ) * (P.arc d).initialDirection,
    hinterior, hz'⟩




theorem boundaryGluing_face_arc_component
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hinc : (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior ∩ closure F.val).Nonempty)
    {z : ℂ} (hz : z ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior) :
    F.val ⊆ connectedComponentIn
      (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P) z := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨u, hu, huF⟩ := hinc
  obtain ⟨a, ha, hF⟩ := F.property
  have hconn : IsPreconnected F.val := by
    rw [hF]
    exact (isConnected_connectedComponentIn_iff.mpr ha).isPreconnected
  have hins : IsPreconnected (insert u F.val) :=
    hconn.subset_closure (Set.subset_insert _ _)
      (Set.insert_subset huF subset_closure)
  have hsub : insert u F.val ⊆
      m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
    apply Set.insert_subset
    · exact ⟨m0Geodesic_arc_subset_ambient hp e hu.1, fun huP =>
        Set.disjoint_left.mp
          (boundaryGluing_arc_interior_disjoint_trace W h k longest hp P he) hu huP⟩
    · intro q hq
      exact ⟨hFR hq, fun hqP => G.face_subset_compl F hq
        (m0GeodesicTrace_subset_drawing hp P hqP)⟩
  have hcomp := hins.subset_connectedComponentIn (Set.mem_insert u F.val) hsub
  have hucomp := (boundaryGluing_arc_interior_subset_component
    W h k longest hp P he hz).1 hu
  have hEq := connectedComponentIn_eq hucomp
  intro q hq
  rw [hEq]
  exact hcomp (Set.mem_insert_of_mem u hq)




theorem boundaryGluing_sideEdges_iff_incidentFace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hinc : (((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).interior ∩ closure F.val).Nonempty)
    (s : ThinMapSide) :
    e ∈ (m0GeodesicSide hp P s).edges ↔
      F.val ⊆ m0GeodesicSideOpenRegion hp P s := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨z, hz⟩ := gluing_arc_interior_nonempty G (wholePlaneDartι W 0 (e, false))
  have hcomp := boundaryGluing_face_arc_component W h k longest hp P he F hFR hinc hz
  have hcrit := boundaryGluing_sideEdges_iff_interiorPoint W h k longest hp P he hz
  obtain ⟨a, ha, hF⟩ := F.property
  have haF : a ∈ F.val := hF ▸ mem_connectedComponentIn ha
  have hacomp := hcomp haF
  have hleft : a ∈ m0GeodesicLeftOpen hp P ↔ z ∈ m0GeodesicLeftOpen hp P := by
    constructor
    · intro haL
      have hca := connectedComponentIn_eq haL
      have hcz := connectedComponentIn_eq hacomp
      have hzR : z ∈ m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P :=
        ⟨m0Geodesic_arc_subset_ambient hp e hz.1, fun hzP =>
          Set.disjoint_left.mp
            (boundaryGluing_arc_interior_disjoint_trace W h k longest hp P he) hz hzP⟩
      change z ∈ connectedComponentIn
        (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P)
        (G.pos ((m0CutData W H h hLL).x (k - 1)))
      rw [hca, ← hcz]
      exact mem_connectedComponentIn hzR
    · intro hzL
      change a ∈ connectedComponentIn
        (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P)
        (G.pos ((m0CutData W H h hLL).x (k - 1)))
      rw [connectedComponentIn_eq hzL]
      exact hacomp
  obtain ⟨t, ht, huniq⟩ := m0GeodesicFace_exactly_one hp P F hFR
  have hlabel : ∀ t : ThinMapSide,
      F.val ⊆ m0GeodesicSideOpenRegion hp P t ↔
        a ∈ m0GeodesicSideOpenRegion hp P t := by
    intro b
    constructor
    · exact fun hb => hb haF
    · intro hab
      have hbt : b = t := by
        cases b <;> cases t
        · rfl
        · exact False.elim (Set.disjoint_left.mp
            (m0GeodesicSideOpenRegion_disjoint hp P) hab (ht haF))
        · exact False.elim (Set.disjoint_left.mp
            (m0GeodesicSideOpenRegion_disjoint hp P) (ht haF) hab)
        · rfl
      exact hbt ▸ ht
  cases s with
  | left => exact hcrit.1.trans (hleft.symm.trans (hlabel .left).symm)
  | right =>
    rw [hlabel]
    constructor
    · intro hr
      refine ⟨hFR haF, ?_⟩
      intro haCl
      have haNot : a ∉ m0GeodesicTrace hp P := fun haP =>
        G.face_subset_compl F haF (m0GeodesicTrace_subset_drawing hp P haP)
      exact (hcrit.2.mp hr) (hleft.mp
        (m0GeodesicLeftOpen_closure_inter_complement_subset hp P
          ⟨haCl, hFR haF, haNot⟩))
    · intro haR
      apply hcrit.2.mpr
      intro hzL
      exact haR.2 (subset_closure (hleft.mpr hzL))




theorem boundaryGluing_sideEdges_iff_borderingFace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) (b : Bool)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (e, b)) F) (s : ThinMapSide) :
    e ∈ (m0GeodesicSide hp P s).edges ↔
      F.val ⊆ m0GeodesicSideOpenRegion hp P s := by
  apply boundaryGluing_sideEdges_iff_incidentFace W h k longest hp P he F hFR
  have hinc := gluing_dartBorders_arcInterior_closure
    (WholePlanePastGlueDrawing.glueDrawing W h hp H)
    (wholePlaneDartι W 0 (e, b)) F hb
  cases b with
  | false => exact hinc
  | true =>
    have hf := (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc_flip
      (wholePlaneDartι W 0 (e, false))
    change (WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, true)) = _ at hf
    rw [hf, Polyline.interior_reverse_transfer] at hinc
    exact hinc




theorem boundaryGluing_retained_borderingFace_exists
    (hp : BoundaryHitWitnesses (kmswPastCode W)) (e : ℕ) :
    ∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      F.val ⊆ m0GeodesicAmbientRegion W H h ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (e, false)) F := by
  classical
  let w := shiftedStream W 0
  have hL : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  have hR : ∀ a : ℤ, ∃ n, KMSW.R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    change KMSW.R w n = -(max (-a) 1) at hn
    exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩
  obtain ⟨j, hj, _⟩ : ∃! j : TriangleCreationTime w,
      (e, false) ∈ stageTriangleDartList w j := by
    rcases kmswRunInfDart_partition w (H.1 0) hL hR (e, false) with
      ⟨f, _, hf⟩ | ⟨f, _, hf⟩ | hj
    · exact Bool.noConfusion (congrArg Prod.snd hf)
    · exact Bool.noConfusion (congrArg Prod.snd hf)
    · exact hj
  let F0 := capFace w (H.1 0) j
  have hF0 := capFace_isBounded_face w (H.1 0) j
  obtain ⟨F, hF, hb⟩ := WholePlaneGlueFaceOrbits.glueFaceOrbits_runZero_dartBorders
    W h hp H (e, false) F0 hF0
  refine ⟨F, ?_, hb.mpr ((cap_border_iff w (H.1 0) j (e, false)).mpr hj)⟩
  intro z hz
  have hup := boundedFace_subset_upper w h (H.1 0) F0 hF0 (hF ▸ hz)
  change seamFun w h (H.1 0) z.re < z.im at hup
  exact le_of_lt hup





theorem boundaryGluing_sideEdges_iff_exists_borderingFace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) (s : ThinMapSide) :
    e ∈ (m0GeodesicSide hp P s).edges ↔
      ∃ (b : Bool) (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face),
        F.val ⊆ m0GeodesicAmbientRegion W H h ∧
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 (e, b)) F ∧
        F.val ⊆ m0GeodesicSideOpenRegion hp P s := by
  constructor
  · intro hs
    obtain ⟨F, hFR, hb⟩ := boundaryGluing_retained_borderingFace_exists W h hp e
    exact ⟨false, F, hFR, hb,
      (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
        false F hFR hb s).mp hs⟩
  · rintro ⟨b, F, hFR, hb, hs⟩
    exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
      b F hFR hb s).mpr hs




theorem boundaryGluing_sideEdges_iff_forall_borderingFace
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) (s : ThinMapSide) :
    e ∈ (m0GeodesicSide hp P s).edges ↔
      ∀ (b : Bool) (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face),
        F.val ⊆ m0GeodesicAmbientRegion W H h →
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 (e, b)) F →
        F.val ⊆ m0GeodesicSideOpenRegion hp P s := by
  constructor
  · intro hs b F hFR hb
    exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
      b F hFR hb s).mp hs
  · intro hall
    obtain ⟨F, hFR, hb⟩ := boundaryGluing_retained_borderingFace_exists W h hp e
    exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
      false F hFR hb s).mpr (hall false F hFR hb)




theorem boundaryGluing_faceSide_iff_of_dualChain
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {F F' : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face}
    (hchain : Relation.ReflTransGen
      (fun A B : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face =>
        ∃ e : ℕ, e ∉ m0GeodesicEdges P ∧ ∃ b c : Bool,
          A.val ⊆ m0GeodesicAmbientRegion W H h ∧
          B.val ⊆ m0GeodesicAmbientRegion W H h ∧
          (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
            (wholePlaneDartι W 0 (e, b)) A ∧
          (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
            (wholePlaneDartι W 0 (e, c)) B) F F')
    (s : ThinMapSide) :
    (F.val ⊆ m0GeodesicSideOpenRegion hp P s) ↔
      F'.val ⊆ m0GeodesicSideOpenRegion hp P s := by
  induction hchain with
  | refl => exact Iff.rfl
  | @tail A B _ hstep ih =>
    obtain ⟨e, he, b, c, hAR, hBR, hA, hB⟩ := hstep
    exact ih.trans
      ((boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
          b A hAR hA s).symm.trans
        (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
          c B hBR hB s))





theorem boundaryGluing_outgoing_arg_lt_iff
    (hfin : KMSWFiniteIncidence (shiftedStream W 0))
    (hfinS : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hL : ∀ n, 0 ≤ L (hatCodes (boundaryGluingFutureStream W h k) hτ) n)
    (htrans : Filter.Tendsto (L (hatCodes (boundaryGluingFutureStream W h k) hτ))
      Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R (hatCodes (boundaryGluingFutureStream W h k) hτ) n ≤ a)
    (a e f : ℕ)
    (he : EdgePresent (hatCodes (boundaryGluingFutureStream W h k) hτ) e ∧
      edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) e = a)
    (hf : EdgePresent (hatCodes (boundaryGluingFutureStream W h k) hτ) f ∧
      edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) f = a) :
    let z := hatCodes (boundaryGluingFutureStream W h k) hτ
    let hz := hatCodes_inducedFiniteIncidence (boundaryGluingFutureStream W h k) hτ hfinS
    let A := monotoneFamilyDrawing z hz (monotone_family_all z)
    let G := monotoneFamilyDrawing (shiftedStream W 0) hfin
      (monotone_family_all (shiftedStream W 0))
    Complex.arg (A.arc (e, false)).initialDirection <
        Complex.arg (A.arc (f, false)).initialDirection ↔
      Complex.arg (G.arc (boundaryGluingHatEdgeMap W h k hτ e, false)).initialDirection <
        Complex.arg (G.arc (boundaryGluingHatEdgeMap W h k hτ f, false)).initialDirection := by
  classical
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let z := hatCodes u hτ
  let hz := hatCodes_inducedFiniteIncidence u hτ hfinS
  let ha := kmsw_vertex_allocated_of_finite_incidence z hz a
  let es := kmswOutgoingEdgesLeftToRight z hz hL htrans hR a ha
  let φ := boundaryGluingHatEdgeMap W h k hτ
  let G := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let hfam : ∀ n, ∃ A : StageDrawing z n, Nonempty (MonotoneStageInvariant z n A) :=
    fun n => ⟨monotoneLayoutDrawing z n ((monotone_family_all z) n).choose,
      ((monotone_family_all z) n).choose_spec⟩
  have hem : e ∈ es := (mem_kmswOutgoingEdgesLeftToRight z hz hL htrans hR a ha e).mpr he
  have hfm : f ∈ es := (mem_kmswOutgoingEdgesLeftToRight z hz hL htrans hR a ha f).mpr hf
  have hidx := kmswOutgoingEdgesLeftToRight_idxOf_lt_iff_arg_lt z hz hfam
    hL htrans hR a ha f e hfm hem
  have hφ (b : ℕ) : φ b = kmswShiftEdgeMapAll w t
      (hatLimitEdgeMap u hτ b) (hatLimitEdgeMap u hτ b) :=
    boundaryGluingEdgeMap_eq_shift W h k _
  have hvertex : edgeWest w (φ e) = edgeWest w (φ f) := by
    have he' := (shiftHat_edge_incidence w t hτ e).1
    have hf' := (shiftHat_edge_incidence w t hτ f).1
    dsimp only at he' hf'
    erw [← hφ e] at he'
    erw [← hφ f] at hf'
    exact he'.trans ((congrArg
      (fun b => limitVertexMap (kmswShiftVertexMapAll w t) u (hatLimitVertexMap u hτ b))
      (he.2.trans hf.2.symm)).trans hf'.symm)
  constructor
  · intro harg
    have hi : es.idxOf f < es.idxOf e := hidx.mpr harg
    have hle := boundaryGluing_outgoing_index_arg_le W h k hτ
      hfin hfinS hL htrans hR a f e hf he hi.le
    apply lt_of_le_of_ne hle
    intro heq
    have hef : e = f := boundaryGluingHatEdgeMap_injective W h k hτ
      (congrArg Prod.fst (G.initial_arg_injective (φ e, false) (φ f, false)
        hvertex heq))
    subst f
    exact (lt_irrefl _ harg)
  · intro harg
    apply hidx.mp
    by_contra hi
    have hle := boundaryGluing_outgoing_index_arg_le W h k hτ
      hfin hfinS hL htrans hR a e f he hf (Nat.le_of_not_gt hi)
    exact (not_lt_of_ge hle) harg





theorem boundaryGluing_previous_boundary_face_left
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (b : Bool) (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (boundaryOuterEdge (shiftedStream W 0) h (k - 1), b)) F) :
    F.val ⊆ m0GeodesicSideOpenRegion hp P .left := by
  obtain ⟨hl, hr, _⟩ := boundaryGluing_previous_boundary_edge_left W h k longest hp P
  have he : boundaryOuterEdge (shiftedStream W 0) h (k - 1) ∉ m0GeodesicEdges P := by
    intro he
    exact hr ((m0GeodesicEdges_subset_both hp P he).2)
  exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
    b F hFR hb .left).mp hl

end RemainingObligations




theorem boundaryGluing_hatSideEdges_iff_arc (s : ThinMapSide) (e : ℕ) :
    let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
      ⟨boundaryFutureHattedPath k W, hq⟩
    let w := boltzmannKMSWStream (pathCode q.val)
    let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
    boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingHatSideEdges W h k hτ x hq s ↔
      ((monotoneFamilyDrawing w hf (monotone_family_all w)).arc (e, false)).image ⊆
        thinMapSideRegion w hf
          (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
          (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
          (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
          (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) s := by
  dsimp only
  have himage : boundaryGluingHatEdgeMap W h k hτ e ∈
      boundaryGluingHatSideEdges W h k hτ x hq s ↔
      e ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s
        ⟨boundaryFutureHattedPath k W, hq⟩).edges := by
    constructor
    · rintro ⟨a, ha, hae⟩
      exact (boundaryGluingHatEdgeMap_injective W h k hτ hae) ▸ ha
    · intro he
      exact ⟨e, he, rfl⟩
  rw [himage]
  change e ∈ ⋃ j, geometricAncestorEdges x renewalTime
    renewalTime_positiveSuccessTime s ⟨boundaryFutureHattedPath k W, hq⟩ j ↔ _
  rw [iUnion_geometricAncestorEdges]
  rfl





theorem boundaryGluing_hatSideEdges_iff_seed (s : ThinMapSide) (e : ℕ)
    (he : ∀ i : ℕ, e ≠ (sourceAncestorPath x renewalTime
      renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hq⟩).edge i) :
    let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
      ⟨boundaryFutureHattedPath k W, hq⟩
    let w := boltzmannKMSWStream (pathCode q.val)
    let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
    boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingHatSideEdges W h k hτ x hq s ↔
      thinMapArcSeed w hf e ∈ thinMapSideRegion w hf
        (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
        (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
        (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
        (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) s := by
  dsimp only
  exact (boundaryGluing_hatSideEdges_iff_arc W h k hτ x hq s e).trans
    (thinMapArc_subset_sideRegion_iff_seed _ _ _ _ _ _ s e he)




theorem boundaryGluing_hatSideEdges_iff_launch_arg (s : ThinMapSide) (e i : ℕ)
    (he : EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e)
    (hi : edgeWest (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e =
      ((sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime
        ⟨boundaryFutureHattedPath k W, hq⟩).initial i).1.id)
    (hoff : ∀ j : ℕ, e ≠ (sourceAncestorPath x renewalTime
      renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hq⟩).edge j) :
    let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
      ⟨boundaryFutureHattedPath k W, hq⟩
    let w := boltzmannKMSWStream (pathCode q.val)
    let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
    let G := monotoneFamilyDrawing w hf (monotone_family_all w)
    let P := sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q
    boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingHatSideEdges W h k hτ x hq s ↔
      match s with
      | .left => Complex.arg (G.arc (P.edge i, false)).initialDirection <
          Complex.arg (G.arc (e, false)).initialDirection
      | .right => Complex.arg (G.arc (e, false)).initialDirection <
          Complex.arg (G.arc (P.edge i, false)).initialDirection := by
  dsimp only
  exact (boundaryGluing_hatSideEdges_iff_seed W h k hτ x hq s e hoff).trans
    (thinMapArcSeed_mem_side_iff_launch_arg _ _ _ _ _ _ e he i hi hoff s)





theorem boundaryGluing_hatSideEdges_iff_glued_launch_arg
    (H : WholePlaneRotationHypothesis W)
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (s : ThinMapSide) (e i : ℕ)
    (he : EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e)
    (hi : edgeWest (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e =
      ((sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime
        ⟨boundaryFutureHattedPath k W, hq⟩).initial i).1.id)
    (hoff : ∀ j : ℕ, e ≠ (sourceAncestorPath x renewalTime
      renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hq⟩).edge j) :
    let P := sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hq⟩
    let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
    let φ := boundaryGluingHatEdgeMap W h k hτ
    boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingHatSideEdges W h k hτ x hq s ↔
      match s with
      | .left => Complex.arg (G.arc (wholePlaneDartι W 0 (φ (P.edge i), false))
          ).initialDirection <
          Complex.arg (G.arc (wholePlaneDartι W 0 (φ e, false))).initialDirection
      | .right => Complex.arg (G.arc (wholePlaneDartι W 0 (φ e, false))
          ).initialDirection <
          Complex.arg (G.arc (wholePlaneDartι W 0 (φ (P.edge i), false))).initialDirection := by
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  let P := sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q
  have hc := boundaryGluing_decoded_stream W h k hτ
  have hL := sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q
  have ht := sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q
  have hR := sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q
  rw [hc] at hL ht hR
  have heH : EdgePresent (hatCodes (boundaryGluingFutureStream W h k) hτ) e ∧
      edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) e = (P.initial i).1.id := by
    rw [← hc]
    exact ⟨he, hi⟩
  have hpH : EdgePresent (hatCodes (boundaryGluingFutureStream W h k) hτ) (P.edge i) ∧
      edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) (P.edge i) =
        (P.initial i).1.id := by
    rw [← hc]
    exact P.edge_outgoing_at_initial _ i
  have hleft := boundaryGluing_outgoing_arg_lt_iff W h k hτ (H.1 0)
    hfin hL ht hR (P.initial i).1.id (P.edge i) e hpH heH
  have hright := boundaryGluing_outgoing_arg_lt_iff W h k hτ (H.1 0)
    hfin hL ht hR (P.initial i).1.id e (P.edge i) heH hpH
  have hcongr (u v : ℕ → Fin 3) (hu : KMSWFiniteIncidence u)
      (hv : KMSWFiniteIncidence v) (huv : u = v) (d : ℕ × Bool) :
      (monotoneFamilyDrawing u hu (monotone_family_all u)).arc d =
        (monotoneFamilyDrawing v hv (monotone_family_all v)).arc d := by
    subst v
    rfl
  have harc := hcongr _ _
    (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
    (hatCodes_inducedFiniteIncidence (boundaryGluingFutureStream W h k) hτ hfin) hc
  dsimp only at hleft hright
  rw [← harc (P.edge i, false), ← harc (e, false)] at hleft
  rw [← harc (P.edge i, false), ← harc (e, false)] at hright
  have hside := boundaryGluing_hatSideEdges_iff_launch_arg W h k hτ x hq s e i he hi hoff
  cases s with
  | left =>
    dsimp only at hside ⊢
    simp only [WholePlanePastGlueM0Restriction.restrict_arc]
    exact hside.trans hleft
  | right =>
    dsimp only at hside ⊢
    simp only [WholePlanePastGlueM0Restriction.restrict_arc]
    exact hside.trans hright






theorem boundaryGluing_finiteCut_sideEdges_iff (x : XDP)
    (w : ℕ → Fin 3) (hf : KMSWFiniteIncidence w)
    (hL : ∀ j, 0 ≤ L w j) (ht : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hRneg : ∀ a : ℤ, ∃ n, R w n ≤ a) (Q : InfinitePresentPath w ⟨0⟩)
    (t : ℕ) {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => Q.edge j.val))
    (s : ThinMapSide) (d : Fin R.dartCount) :
    (I.toEquiv d).1.val ∈ sideEdges w hf hL ht hRneg Q s ↔
      match s with
      | .left => d ∈ pathCutLeftHalfDarts R.B (selectedGeodesicOfLen R.B x hR)
      | .right => d ∈ pathCutRightHalfDarts R.B (selectedGeodesicOfLen R.B x hR) := by
  have hseam (a : ThinMapSide) :
      AncestorPosHalfSeamLaunchArcSeeds w hf hL ht hRneg Q t R hR I a := by
    apply (ancestorPos_seamLaunch_iff_argumentOrder
      w hf hL ht hRneg Q t R hR I hp a).mpr
    intro i
    exact ancestorPos_seamLaunch_argumentOrder w hf hL ht hRneg Q t R hR I hp a i
  have hseed (a : ThinMapSide) :
      AncestorPosHalfOffPrefixArcSeedIdentification w hf hL ht hRneg Q t R hR I a :=
    (ancestorPos_arcSeeds_iff_boundaryLaunch w hf hL ht hRneg Q t R hR I hp a).mpr
      ((ancestorPos_boundaryLaunch_iff_seamLaunch
        w hf hL ht hRneg Q t R hR I hp a).mpr (hseam a))
  have hside := (ancestorPos_sideRanges_iff_arcSeeds
    w hf hL ht hRneg Q t R hR I hp).mpr hseed
  calc
    (I.toEquiv d).1.val ∈ sideEdges w hf hL ht hRneg Q s ↔
        stageLimitDart w t (I.toEquiv d) ∈ Set.range (ancestorPosDartId w t R hR I s) :=
      (hside s (I.toEquiv d)).symm
    _ ↔ d ∈ Set.range (ancestorPosDartMap R hR s) :=
      ancestorPos_stage_range_iff w t R hR I s d
    _ ↔ _ := by rw [ancestorPosDartMap_range]; cases s <;> rfl





theorem boundaryGluing_hatSideEdges_iff_finiteCut
    (t : ℕ) {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) t))
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m =>
        (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime
          ⟨boundaryFutureHattedPath k W, hq⟩).edge j.val))
    (s : ThinMapSide) (d : Fin R.dartCount) :
    boundaryGluingHatEdgeMap W h k hτ (I.toEquiv d).1.val ∈
        boundaryGluingHatSideEdges W h k hτ x hq s ↔
      match s with
      | .left => d ∈ pathCutLeftHalfDarts R.B (selectedGeodesicOfLen R.B x hR)
      | .right => d ∈ pathCutRightHalfDarts R.B (selectedGeodesicOfLen R.B x hR) := by
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  exact (boundaryGluing_hatSideEdges_iff_arc W h k hτ x hq s (I.toEquiv d).1.val).trans
    (boundaryGluing_finiteCut_sideEdges_iff x _
      (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) t R hR I hp s d)






theorem boundaryGluing_hatSideEdges_iff_exists_finiteCut (s : ThinMapSide) (e : ℕ) :
    boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingHatSideEdges W h k hτ x hq s ↔
      ∃ (t ℓ r n m : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
        (I : DirectedMapWithMissingIso R.B.map
          (kmswStageDirectedMap
            (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) t)),
        (((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
          (fun d => d.1.val) = List.ofFn (fun j : Fin m =>
            (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime
              ⟨boundaryFutureHattedPath k W, hq⟩).edge j.val)) ∧
        ∃ d : Fin R.dartCount, (I.toEquiv d).1.val = e ∧
          match s with
          | .left => d ∈ pathCutLeftHalfDarts R.B (selectedGeodesicOfLen R.B x hR)
          | .right => d ∈ pathCutRightHalfDarts R.B (selectedGeodesicOfLen R.B x hR) := by
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  constructor
  · intro he
    have heGeom : e ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s q).edges := by
      obtain ⟨a, ha, hae⟩ := he
      exact (boundaryGluingHatEdgeMap_injective W h k hτ hae) ▸ ha
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp heGeom
    obtain ⟨j, hj⟩ := exists_selectedCut_goodEvent x renewalTime
      renewalTime_positiveSuccessTime a q
    obtain ⟨ℓ, r, n, m, R, hR, I, v, _hrep, _hv, _hroot, _hvt, _hb, hprefix⟩ :=
      sourceAncestorPosHalf_boundary_prefix_embedding x renewalTime
        renewalTime_positiveSuccessTime q s a j hj
    have halloc := (ancestor_edge_in_goodCut_stage x renewalTime
      renewalTime_positiveSuccessTime q s a j hj e ha).1
    let d := I.toEquiv.symm (⟨e, halloc⟩, false)
    have hed : (I.toEquiv d).1.val = e := by
      simp only [d, Equiv.apply_symm_apply]
    refine ⟨_, ℓ, r, n, m, R, hR, I, hprefix, d, hed, ?_⟩
    apply (boundaryGluing_hatSideEdges_iff_finiteCut W h k hτ x hq
      _ R hR I hprefix s d).mp
    rw [hed]
    exact he
  · rintro ⟨t, ℓ, r, n, m, R, hR, I, hprefix, d, hed, hd⟩
    have he := (boundaryGluing_hatSideEdges_iff_finiteCut W h k hτ x hq
      t R hR I hprefix s d).mpr hd
    rw [hed] at he
    exact he





theorem boundaryGluing_hatTriangle_gluedFace
    (H : WholePlaneRotationHypothesis W)
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (T : HatLocalTri (boundaryGluingFutureStream W h k) hτ) :
    ∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      F.val ⊆ m0GeodesicAmbientRegion W H h ∧
      ∀ d ∈ triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) T.val,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 (boundaryGluingHatEdgeMap W h k hτ d.1, d.2)) F := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let A := monotoneFamilyDrawing u hfin (monotone_family_all u)
  let B := hatRealizedDrawing u hfin
  obtain ⟨j, i, F0, Fhat, _hj, _hreach, hi, hF0, hFhat, hb⟩ :=
    hatLocalTriangle_realized u hτ hfin T
  let i' := (stageTriangleRecord_fin_index u j).choose
  have hi' := (stageTriangleRecord_fin_index u j).choose_spec
  have hcaps := monotone_cap_region_eq u
    (familyG u (monotone_family_all u) (j.val + 1))
    (familyG u (monotone_family_all u) (j.val + 1)) i i'
    (hi.trans hi'.symm) (fun _ _ => rfl)
  have hFcap : F0.val = capFace u hfin j :=
    Subtype.ext (hF0.trans (hcaps.trans (capFace_spec u hfin j).1.symm))
  let j0 : TriangleCreationTime w := ⟨t + j.val, j.property⟩
  let Fraw := capFace w (H.1 0) j0
  have hrawBound := capFace_isBounded_face w (H.1 0) j0
  obtain ⟨F, hF, hborder⟩ := WholePlaneGlueFaceOrbits.glueFaceOrbits_runZero_dartBorders
    W h hp H (0, false) Fraw hrawBound
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    have hup := boundedFace_subset_upper w h (H.1 0) Fraw hrawBound (hF ▸ hz)
    change seamFun w h (H.1 0) z.re < z.im at hup
    exact le_of_lt hup
  · intro d hd
    have hdAmbient : A.dartBorders (hatLimitDartEquiv u hτ d).val F0.val :=
      dartBorders_transport B A Fhat.val F0.val
        (hatLimitDartEquiv u hτ d) (hatLimitDartEquiv u hτ d).val
        hFhat.symm rfl (hb d hd)
    have hdj : (hatLimitEdgeMap u hτ d.1, d.2) ∈ stageTriangleDartList u j := by
      exact (cap_border_iff u hfin j _).mp (hFcap ▸ hdAmbient)
    have halloc : hatLimitEdgeMap u hτ d.1 < (kmswStage u (j.val + 1)).nextEdge := by
      apply stage_face_dart_lt_nextEdge u (j.val + 1) (hatLimitEdgeMap u hτ d.1, d.2)
      apply List.mem_append.mpr
      right
      exact List.mem_flatMap.mpr
        ⟨j, (mem_stageTriangleTimes u (j.val + 1) j).mpr (Nat.lt_succ_self _), hdj⟩
    have hrot := kmswWindowPatchData_triangle_rotated w t (j.val + 1) j.val
      (Nat.lt_succ_self _) j.property
    have hmem := hrot.mem_iff.mp
      (List.mem_map.mpr ⟨(hatLimitEdgeMap u hτ d.1, d.2), hdj, rfl⟩)
    have hmap := kmswWindowEdgeMapInf_eq_stage w t (j.val + 1)
      (hatLimitEdgeMap u hτ d.1) halloc
    have hdRaw : (boundaryGluingHatEdgeMap W h k hτ d.1, d.2) ∈
        stageTriangleDartList w j0 := by
      change (kmswWindowEdgeMapInf w t (hatLimitEdgeMap u hτ d.1), d.2) ∈ _
      rw [hmap]
      exact hmem
    have hraw := (cap_border_iff w (H.1 0) j0 _).mpr hdRaw
    have harc := WholePlanePastGlueM0Restriction.restrict_arc W h hp H
      (boundaryGluingHatEdgeMap W h k hτ d.1, d.2)
    exact (PLDrawing.dartBorders_congr _ _ Fraw F harc hF).mpr hraw

/-- Helper toward Lemma 5.5: a fixed oriented dart has only one left
bordering face, by the common point in two sufficiently small wedges. -/
private theorem gluing_border_face_unique {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (G : PLDrawing D V flip rot vert)
    {F F' : G.Face} {d : D} (hF : G.dartBorders d F) (hF' : G.dartBorders d F') :
    F = F' := by
  obtain ⟨a, ha, hF⟩ := hF
  obtain ⟨b, hb, hF'⟩ := hF'
  let t := min a b / 2
  have ht : 0 < t := half_pos (lt_min ha hb)
  have hta : t < a := (half_lt_self (lt_min ha hb)).trans_le (min_le_left _ _)
  have htb : t < b := (half_lt_self (lt_min ha hb)).trans_le (min_le_right _ _)
  exact G.faces_eq_of_mem (hF t t ht hta ht hta) (hF' t t ht htb ht htb)

/-- Helper toward Lemma 5.5: the oriented creation word of a hatted
triangle has a dart, in every creation branch. -/
private theorem gluing_triangle_darts_nonempty (w : ℕ → Fin 3) (T : ℕ × ℕ × ℕ) :
    ∃ d, d ∈ triangleOrientedDarts w T := by
  unfold triangleOrientedDarts
  split <;> exact ⟨_, List.mem_cons_self⟩





theorem boundaryGluing_hatTriangle_dualChain_side_iff
    {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    (longest : Bool) (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    {T U : HatLocalTri (boundaryGluingFutureStream W h k) hτ}
    (hchain : Relation.ReflTransGen
      (fun A B : HatLocalTri (boundaryGluingFutureStream W h k) hτ =>
        ∃ d : ℕ × Bool,
          d ∈ triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) A.val ∧
          (d.1, !d.2) ∈
            triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) B.val ∧
          boundaryGluingHatEdgeMap W h k hτ d.1 ∉ m0GeodesicEdges P) T U)
    (F F' : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hF'R : F'.val ⊆ m0GeodesicAmbientRegion W H h)
    (hF : ∀ d ∈ triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) T.val,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (boundaryGluingHatEdgeMap W h k hτ d.1, d.2)) F)
    (hF' : ∀ d ∈ triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) U.val,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (boundaryGluingHatEdgeMap W h k hτ d.1, d.2)) F')
    (s : ThinMapSide) :
    (F.val ⊆ m0GeodesicSideOpenRegion hp P s) ↔
      F'.val ⊆ m0GeodesicSideOpenRegion hp P s := by
  induction hchain generalizing F' with
  | refl =>
    obtain ⟨d, hd⟩ := gluing_triangle_darts_nonempty
      (hatCodes (boundaryGluingFutureStream W h k) hτ) T.val
    have heq := gluing_border_face_unique
      (WholePlanePastGlueDrawing.glueDrawing W h hp H) (hF d hd) (hF' d hd)
    rw [heq]
  | @tail A B _ hstep ih =>
    obtain ⟨Fmid, hmidR, hmid⟩ := boundaryGluing_hatTriangle_gluedFace W h k hτ H hp hfin A
    have hprev := ih Fmid hmidR hmid
    obtain ⟨d, hdA, hdB, he⟩ := hstep
    exact hprev.trans
      ((boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
          d.2 Fmid hmidR (hmid d hdA) s).symm.trans
        (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
          (!d.2) F' hF'R (hF' (d.1, !d.2) hdB) s))

/-! The following local seeds concern the actual glued components. -/

/-- Helper toward Lemma 5.5: raising a point of a continuous graph ray
connects it to the boundary west of the root inside the ambient epigraph. -/
private theorem gluing_graphRay_raise_mem_component
    {S : Set ℂ} {x₀ a : ℝ} {X : WithTop ℝ} {g f : ℝ → ℝ}
    (hgraph : S = {z | z.re ∈ rayDomain x₀ X ∧ z.im = g z.re})
    (hg : ContinuousOn g (rayDomain x₀ X)) (hf : Continuous f)
    (ha : a < x₀) {z : ℂ} (hz : z ∈ S) (hzf : f z.re ≤ z.im)
    {ε : ℝ} (hε : 0 < ε) :
    (⟨z.re, z.im + ε⟩ : ℂ) ∈
      connectedComponentIn ({q : ℂ | f q.re ≤ q.im} \ S) (⟨a, f a⟩ : ℂ) := by
  have hzg := hz
  rw [hgraph] at hzg
  let b := z.re
  let roof : ℝ → ℝ := fun x => max (f x) (g (max x₀ x)) + ε
  have hab : a ≤ b := ha.le.trans hzg.1.1
  have hmap : Set.MapsTo (fun x : ℝ => max x₀ x) (Set.Icc a b) (rayDomain x₀ X) := by
    intro x hx
    exact ⟨le_max_left _ _, lt_of_le_of_lt
      (WithTop.coe_le_coe.mpr (max_le hzg.1.1 hx.2)) hzg.1.2⟩
  have hroof : ContinuousOn roof (Set.Icc a b) :=
    (continuous_max.comp_continuousOn (hf.continuousOn.prodMk
      (hg.comp (continuous_const.max continuous_id).continuousOn hmap))).add continuousOn_const
  let V : Set ℂ := (fun y : ℝ => (⟨a, y⟩ : ℂ)) '' Set.Icc (f a) (roof a)
  let T := graphOver a b roof ∪ V
  have hfa : f a ≤ roof a :=
    (le_max_left _ _).trans (le_add_of_nonneg_right hε.le)
  have hV : IsPreconnected V :=
    isPreconnected_Icc.image (fun y : ℝ => (⟨a, y⟩ : ℂ)) (by
      simp only [Complex.mk_eq_add_mul_I]
      fun_prop)
  have hT : IsPreconnected T := by
    exact IsPreconnected.union'
      ⟨⟨a, roof a⟩, ⟨le_rfl, hab, rfl⟩, ⟨roof a, ⟨hfa, le_rfl⟩, rfl⟩⟩
      (isPathConnected_graphOver hab hroof).isConnected.isPreconnected hV
  have hTS : T ⊆ {q : ℂ | f q.re ≤ q.im} \ S := by
    rintro q (hq | hq)
    · have hqroof : q.im = roof q.re := hq.2.2
      refine ⟨?_, ?_⟩
      · change f q.re ≤ q.im
        rw [hqroof]
        exact (le_max_left _ _).trans (le_add_of_nonneg_right hε.le)
      · intro hqS
        rw [hgraph] at hqS
        have hqmax : max x₀ q.re = q.re := max_eq_right hqS.1.1
        have hlt : g q.re < roof q.re := by
          dsimp [roof]
          rw [hqmax]
          exact lt_of_le_of_lt (le_max_right _ _) (lt_add_of_pos_right _ hε)
        exact (ne_of_lt hlt) (hqS.2.symm.trans hqroof)
    · obtain ⟨y, hy, rfl⟩ := hq
      refine ⟨hy.1, ?_⟩
      intro hqS
      rw [hgraph] at hqS
      exact (not_le_of_gt ha) hqS.1.1
  have hbase : (⟨a, f a⟩ : ℂ) ∈ T :=
    Or.inr ⟨f a, ⟨le_rfl, hfa⟩, rfl⟩
  apply hT.subset_connectedComponentIn hbase hTS
  apply Or.inl
  refine ⟨hab, le_rfl, ?_⟩
  change z.im + ε = max (f z.re) (g (max x₀ z.re)) + ε
  rw [max_eq_right hzg.1.1, ← hzg.2, max_eq_right hzf]

/-- Helper toward Lemma 5.5: the hatted vertex embedding into run zero,
using the same coherent stage maps as the geometric edge embedding. -/
@[expose] noncomputable def boundaryGluingHatVertexMap : ℕ → ℕ :=
  fun a => limitVertexMap
    (kmswShiftVertexMapAll (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k))
    (boundaryGluingFutureStream W h k)
    (hatLimitVertexMap (boundaryGluingFutureStream W h k) hτ a)

/-- Helper toward Lemma 5.5: the hatted embedding preserves both geometric
endpoints, including endpoints of missing edges. -/
theorem boundaryGluing_hat_edge_endpoints (e : ℕ) :
    edgeWest (shiftedStream W 0) (boundaryGluingHatEdgeMap W h k hτ e) =
      boundaryGluingHatVertexMap W h k hτ
        (edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) e) ∧
    edgeEast (shiftedStream W 0) (boundaryGluingHatEdgeMap W h k hτ e) =
      boundaryGluingHatVertexMap W h k hτ
        (edgeEast (hatCodes (boundaryGluingFutureStream W h k) hτ) e) := by
  have he := shiftHat_edge_incidence (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k) hτ e
  dsimp only at he
  erw [← boundaryGluingEdgeMap_eq_shift W h k] at he
  exact ⟨he.1, he.2.1⟩

/-- Helper toward Lemma 5.5: no two hatted vertices are identified by gluing. -/
theorem boundaryGluingHatVertexMap_injective :
    Function.Injective (boundaryGluingHatVertexMap W h k hτ) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  have hshift : Function.Injective (limitVertexMap (kmswShiftVertexMapAll w t) u) := by
    intro a b hab
    obtain ⟨m, hm⟩ := kmswVertexAllocated_all u ⟨a⟩
    obtain ⟨n, hn⟩ := kmswVertexAllocated_all u ⟨b⟩
    have ha := hm.trans_le (CutConverse.nextVertex_mono u (Nat.le_max_left m n))
    have hb := hn.trans_le (CutConverse.nextVertex_mono u (Nat.le_max_right m n))
    have hma : limitVertexMap (kmswShiftVertexMapAll w t) u a =
        kmswShiftVertexMapAll w t (max m n) a :=
      limitVertexMap_eq_of_allocated _ (kmswShiftVertexMapAll_extend w t) _ _ ha
    have hmb : limitVertexMap (kmswShiftVertexMapAll w t) u b =
        kmswShiftVertexMapAll w t (max m n) b :=
      limitVertexMap_eq_of_allocated _ (kmswShiftVertexMapAll_extend w t) _ _ hb
    rw [hma, hmb] at hab
    exact (kmswShift_sim2_all w t (max m n)).sim.vertex_injective a b ha hb hab
  intro a b hab
  apply vertex_inj (hatLimitExplicitInput u hτ)
    (kmswVertexAllocated_all _ ⟨a⟩) (kmswVertexAllocated_all _ ⟨b⟩)
  exact hshift hab

section GluedSeamSeeds

variable {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  (longest : Bool) (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)




theorem boundaryGluing_above_trace_mem_leftOpen {y z : ℂ}
    (hy : y ∈ m0GeodesicTrace hp P) (hre : y.re = z.re) (him : y.im < z.im) :
    z ∈ m0GeodesicLeftOpen hp P := by
  let f := seamFun (shiftedStream W 0) h (H.1 0)
  let a := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  have hbase : (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x (k - 1)) = (⟨a, f a⟩ : ℂ) := by
    rw [(m0CutData W H h hLL).x_eq h hLL (k - 1), m0Geodesic_pos_runZero hp]
    exact boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) (k - 1)
  obtain ⟨X, g, _, hg, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp P
  have hraise := gluing_graphRay_raise_mem_component hgraph hg
    (seamFun_continuous (shiftedStream W 0) h (H.1 0))
    (seamX_strictMono (shiftedStream W 0) h (H.1 0) (show k - 1 < k by omega))
    hy (m0GeodesicTrace_subset_ambient hp P hy) (sub_pos.mpr him)
  have hz : (⟨y.re, y.im + (z.im - y.im)⟩ : ℂ) = z := by
    apply Complex.ext
    · exact hre
    · change y.im + (z.im - y.im) = z.im
      ring
  rw [hz] at hraise
  unfold m0GeodesicLeftOpen
  rw [hbase]
  exact hraise

/-- Helper toward Lemma 5.5: the first monotone segment realizes its
polyline height at every abscissa between its endpoints. -/
private theorem gluing_first_segment_mem (p : Polyline) (hm : p.XMonotone)
    (hlen : 2 ≤ p.points.length) (x : ℝ)
    (hx : x ∈ Set.Icc p.start.re (p.point 1).re) :
    (⟨x, p.heightFn x⟩ : ℂ) ∈ p.image := by
  have hr := p.point_re_lt hm (show 0 < 1 by omega) (show 1 < _ by omega)
  rw [p.point_zero_eq_start] at hr
  refine Or.inr ⟨0, by omega, ?_⟩
  rw [Polyline.segmentAt, p.point_zero_eq_start, mem_segment_iff_height hr]
  refine ⟨hx.1, hx.2, ?_⟩
  have hh := p.heightFn_linear_on_segment hm (i := 0) (by omega)
    (xval := x) (by simpa only [p.point_zero_eq_start] using hx.1) hx.2
  simpa only [Nat.zero_add, p.point_zero_eq_start, segmentHeight] using hh

/-- Helper toward Lemma 5.5: strict initial angular order realizes an
interior point strictly above the other arc at the same abscissa. -/
private theorem gluing_initial_order_points (p q : Polyline)
    (hp : p.XMonotone) (hq : q.XMonotone)
    (hlenp : 2 ≤ p.points.length) (hlenq : 2 ≤ q.points.length)
    (hs : p.start = q.start)
    (ha : Complex.arg p.initialDirection < Complex.arg q.initialDirection) :
    ∃ z ∈ p.image, ∃ y ∈ q.interior, z.re = y.re ∧ z.im < y.im := by
  have hpdir := p.initialDirection_re_pos hp hlenp
  have hqdir := q.initialDirection_re_pos hq hlenq
  have hsl := (east_arg_lt_iff_slope_lt hpdir hqdir).mp ha
  have hpr : p.start.re < (p.point 1).re := sub_pos.mp hpdir
  have hqr : p.start.re < (q.point 1).re := by
    rw [hs]
    exact sub_pos.mp hqdir
  let b := min (p.point 1).re (q.point 1).re
  let x := (p.start.re + b) / 2
  have hpb : p.start.re < b := lt_min hpr hqr
  have hpx : p.start.re < x := by dsimp only [x]; linarith only [hpb]
  have hxb : x < b := by dsimp only [x]; linarith only [hpb]
  have hxp : x ≤ (p.point 1).re := hxb.le.trans (min_le_left _ _)
  have hxq : x < (q.point 1).re := hxb.trans_le (min_le_right _ _)
  have hpheight := p.heightFn_linear_on_segment hp (i := 0) (by omega)
    (xval := x) (by simpa only [p.point_zero_eq_start] using hpx.le) hxp
  have hqheight := q.heightFn_linear_on_segment hq (i := 0) (by omega)
    (xval := x) (by simpa only [q.point_zero_eq_start, ← hs] using hpx.le) hxq.le
  have hpheight' : p.heightFn x = p.start.im +
      p.initialDirection.im / p.initialDirection.re * (x - p.start.re) := by
    simpa only [Nat.zero_add, p.point_zero_eq_start, Polyline.initialDirection,
      Complex.sub_re, Complex.sub_im] using hpheight
  have hqheight' : q.heightFn x = q.start.im +
      q.initialDirection.im / q.initialDirection.re * (x - q.start.re) := by
    simpa only [Nat.zero_add, q.point_zero_eq_start, Polyline.initialDirection,
      Complex.sub_re, Complex.sub_im] using hqheight
  have hqend : (q.point 1).re ≤ q.finish.re := by
    rw [← q.point_last_eq_finish]
    exact q.point_re_le_of_le hq (by omega) (by omega)
  have hy : (⟨x, q.heightFn x⟩ : ℂ) ∈ q.interior := by
    refine ⟨gluing_first_segment_mem q hq hlenq x
      ⟨by simpa only [← hs] using hpx.le, hxq.le⟩, ?_⟩
    rintro (he | he)
    · have hh := congrArg Complex.re he
      change x = q.start.re at hh
      exact (ne_of_gt hpx) (hh.trans (congrArg Complex.re hs).symm)
    · have hh := congrArg Complex.re he
      change x = q.finish.re at hh
      exact (ne_of_lt (hxq.trans_le hqend)) hh
  refine ⟨⟨x, p.heightFn x⟩, gluing_first_segment_mem p hp hlenp x ⟨hpx.le, hxp⟩,
    ⟨x, q.heightFn x⟩, hy, rfl, ?_⟩
  change p.heightFn x < q.heightFn x
  rw [hpheight', hqheight', ← hs]
  exact add_lt_add_right (mul_lt_mul_of_pos_right hsl (sub_pos.mpr hpx)) _





theorem boundaryGluing_seam_departure_left_of_arg_lt (e i : ℕ)
    (he : e ∉ m0GeodesicEdges P)
    (hi : edgeWest (shiftedStream W 0) e =
      edgeWest (shiftedStream W 0) (P.codePath.edge i))
    (ha : Complex.arg ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (m0GeodesicSeam P i))).initialDirection <
      Complex.arg ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (e, false))).initialDirection) :
    e ∈ (m0GeodesicSide hp P .left).edges := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let A := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hs : (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).start =
      (G.arc (wholePlaneDartι W 0 (e, false))).start := by
    dsimp only [G]
    rw [WholePlanePastGlueM0Restriction.restrict_arc W h hp H (m0GeodesicSeam P i),
      WholePlanePastGlueM0Restriction.restrict_arc W h hp H (e, false),
      A.arc_start, A.arc_start]
    exact congrArg A.pos hi.symm
  obtain ⟨z, hz, y, hy, hre, him⟩ := gluing_initial_order_points
    (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i)))
    (G.arc (wholePlaneDartι W 0 (e, false)))
    (gluing_runZero_arc_graph W h hp (P.codePath.edge i)).2
    (gluing_runZero_arc_graph W h hp e).2 (G.arc_length _) (G.arc_length _) hs ha
  have hyL := boundaryGluing_above_trace_mem_leftOpen W h k longest hp P
    (m0Geodesic_arc_subset_trace hp P i hz) hre him
  exact (boundaryGluing_sideEdges_iff_interiorPoint W h k longest hp P he hy).1.mpr hyL





theorem boundaryGluing_forward_seam_face_left (i : ℕ)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFR : F.val ⊆ m0GeodesicAmbientRegion W H h)
    (hb : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (m0GeodesicSeam P i)) F) :
    F.val ⊆ m0GeodesicSideOpenRegion hp P .left := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let p := G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))
  have hm : p.XMonotone := (gluing_runZero_arc_graph W h hp (P.codePath.edge i)).2
  have hlen : 2 ≤ p.points.length := G.arc_length _
  have hd : 0 < p.initialDirection.re := p.initialDirection_re_pos hm hlen
  let η := (p.point 1).re - p.start.re
  have hη : 0 < η := hd
  let upper : ℝ → ℝ := fun x => p.start.im +
    (p.initialDirection.im / p.initialDirection.re + 1) * (x - p.start.re)
  have hline : ∀ x ∈ Set.Icc p.start.re (p.start.re + η),
      p.heightFn x = p.start.im +
        (p.initialDirection.im / p.initialDirection.re) * (x - p.start.re) := by
    intro x hx
    have hh := p.heightFn_linear_on_segment hm (i := 0) (by omega)
      (xval := x) (by simpa only [p.point_zero_eq_start] using hx.1)
      (by dsimp only [η] at hx; linarith only [hx.2])
    simpa only [Nat.zero_add, p.point_zero_eq_start, Polyline.initialDirection,
      Complex.sub_re, Complex.sub_im] using hh
  obtain ⟨δ, hδ, hw⟩ := wedgeIn_graphRegion_east_lower_slope
    (a := p.start.re) (b := p.start.re + η) (f := p.heightFn) (g := upper)
    p.start p.initialDirection η (p.initialDirection.im / p.initialDirection.re + 1)
    hd le_rfl hη le_rfl hline (lt_add_one _) (fun _ _ => le_rfl)
  obtain ⟨δF, hδF, hwF⟩ := hb
  let t := min δ δF / 2
  have ht : 0 < t := half_pos (lt_min hδ hδF)
  have htδ : t < δ := (half_lt_self (lt_min hδ hδF)).trans_le (min_le_left _ _)
  have htF : t < δF := (half_lt_self (lt_min hδ hδF)).trans_le (min_le_right _ _)
  let z := PlanarMap.wedgePoint p.start p.initialDirection t t
  have hzF : z ∈ F.val := hwF t t ht htF ht htF
  have hz := hw t t ht htδ ht htδ
  change p.start.re < z.re ∧ z.re < p.start.re + η ∧
    p.heightFn z.re < z.im ∧ z.im < upper z.re at hz
  have hq := gluing_first_segment_mem p hm hlen z.re
    ⟨hz.1.le, by dsimp only [η] at hz; linarith only [hz.2.1]⟩
  have hqP : (⟨z.re, p.heightFn z.re⟩ : ℂ) ∈ m0GeodesicTrace hp P :=
    m0Geodesic_arc_subset_trace hp P i hq
  have hzL := boundaryGluing_above_trace_mem_leftOpen W h k longest hp P
    (z := z) hqP rfl hz.2.2.1
  obtain ⟨s, hs, _⟩ := m0GeodesicFace_exactly_one hp P F hFR
  cases s with
  | left => exact hs
  | right =>
    exact False.elim
      (Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp P) hzL (hs hzF))





theorem boundaryGluing_sideEdges_iff_off_trace_point {e : ℕ}
    (he : e ∉ m0GeodesicEdges P) {q : ℂ}
    (hq : q ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).image)
    (hqP : q ∉ m0GeodesicTrace hp P) :
    (e ∈ (m0GeodesicSide hp P .left).edges ↔ q ∈ m0GeodesicLeftOpen hp P) ∧
      (e ∈ (m0GeodesicSide hp P .right).edges ↔ q ∉ m0GeodesicLeftOpen hp P) := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let S := m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P
  obtain ⟨z, hz⟩ := gluing_arc_interior_nonempty G (wholePlaneDartι W 0 (e, false))
  have hqcomp := boundaryGluing_arc_off_trace_subset_component
    W h k longest hp P he hz ⟨hq, hqP⟩
  have hzS : z ∈ S := ⟨m0Geodesic_arc_subset_ambient hp e hz.1,
    fun hzP => Set.disjoint_left.mp
      (boundaryGluing_arc_interior_disjoint_trace W h k longest hp P he) hz hzP⟩
  have hsame : z ∈ m0GeodesicLeftOpen hp P ↔ q ∈ m0GeodesicLeftOpen hp P := by
    constructor
    · intro hzL
      have hc : connectedComponentIn S z = m0GeodesicLeftOpen hp P :=
        (connectedComponentIn_eq hzL).symm
      exact hc ▸ hqcomp
    · intro hqL
      have hcq : connectedComponentIn S q = m0GeodesicLeftOpen hp P :=
        (connectedComponentIn_eq hqL).symm
      have hcz : connectedComponentIn S z = connectedComponentIn S q :=
        connectedComponentIn_eq hqcomp
      have hzself := mem_connectedComponentIn hzS
      rw [hcz, hcq] at hzself
      exact hzself
  have hcrit := boundaryGluing_sideEdges_iff_interiorPoint W h k longest hp P he hz
  exact ⟨hcrit.1.trans hsame, hcrit.2.trans (not_congr hsame)⟩




theorem boundaryGluing_sideEdges_iff_of_shared_point {e f : ℕ}
    (he : e ∉ m0GeodesicEdges P) (hf : f ∉ m0GeodesicEdges P) {q : ℂ}
    (hqe : q ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (e, false))).image)
    (hqf : q ∈ ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (f, false))).image)
    (hqP : q ∉ m0GeodesicTrace hp P) (s : ThinMapSide) :
    e ∈ (m0GeodesicSide hp P s).edges ↔ f ∈ (m0GeodesicSide hp P s).edges := by
  have heq := boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P he hqe hqP
  have hfq := boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P hf hqf hqP
  cases s with
  | left => exact heq.1.trans hfq.1.symm
  | right => exact heq.2.trans hfq.2.symm




theorem boundaryGluing_hat_left_seam_departure
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (e i : ℕ)
    (he : EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e)
    (hi : edgeWest (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e =
      ((sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime
        ⟨boundaryFutureHattedPath k W, hqMode⟩).initial i).1.id)
    (hoff : ∀ j : ℕ, e ≠ (sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩).edge j)
    (hs : boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingLeftHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode) :
    boundaryGluingHatEdgeMap W h k hτ e ∈ (m0GeodesicSide hp P .left).edges := by
  let q : selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime := ⟨boundaryFutureHattedPath k W, hqMode⟩
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime q
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let φ := boundaryGluingHatEdgeMap W h k hτ
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  have heoff : φ e ∉ m0GeodesicEdges P := by
    rintro ⟨j, hj⟩
    exact hoff j (boundaryGluingHatEdgeMap_injective W h k hτ
      (hj.symm.trans (hid j)))
  have hc := boundaryGluing_decoded_stream W h k hτ
  have heq : edgeWest (hatCodes u hτ) e = edgeWest (hatCodes u hτ) (Q.edge i) := by
    rw [← hc]
    exact hi.trans (Q.edge_outgoing_at_initial _ i).2.symm
  have hφ (a : ℕ) : φ a = kmswShiftEdgeMapAll w t
      (hatLimitEdgeMap u hτ a) (hatLimitEdgeMap u hτ a) :=
    boundaryGluingEdgeMap_eq_shift W h k _
  have hew := (shiftHat_edge_incidence w t hτ e).1
  have hpw := (shiftHat_edge_incidence w t hτ (Q.edge i)).1
  dsimp only at hew hpw
  erw [← hφ e] at hew
  erw [← hφ (Q.edge i)] at hpw
  have hwest : edgeWest w (φ e) = edgeWest w (P.codePath.edge i) := by
    rw [hid i]
    exact hew.trans ((congrArg
      (fun a => limitVertexMap (kmswShiftVertexMapAll w t) u (hatLimitVertexMap u hτ a))
      heq).trans hpw.symm)
  have harg := (boundaryGluing_hatSideEdges_iff_glued_launch_arg W h k hτ
    (if longest then XDP.ldp else XDP.sdp) hqMode H hp hfin .left e i he hi hoff).mp hs
  apply boundaryGluing_seam_departure_left_of_arg_lt W h k longest hp P
    (φ e) i heoff hwest
  change Complex.arg ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (P.codePath.edge i, false))).initialDirection < _
  rw [hid i]
  exact harg






theorem boundaryGluing_hatTriangle_reachable_from_seam_left
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (i : ℕ) (T U : HatLocalTri (boundaryGluingFutureStream W h k) hτ)
    (hseed : ((sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩).edge i, false) ∈
        triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) T.val)
    (hchain : Relation.ReflTransGen
      (fun A B : HatLocalTri (boundaryGluingFutureStream W h k) hτ =>
        ∃ d : ℕ × Bool,
          d ∈ triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) A.val ∧
          (d.1, !d.2) ∈
            triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) B.val ∧
          d.1 ∉ Set.range (sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime
            ⟨boundaryFutureHattedPath k W, hqMode⟩).edge) T U)
    (d : ℕ × Bool)
    (hd : d ∈ triangleOrientedDarts
      (hatCodes (boundaryGluingFutureStream W h k) hτ) U.val) :
    boundaryGluingHatEdgeMap W h k hτ d.1 ∈ (m0GeodesicSide hp P .left).edges := by
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  have hchain' : Relation.ReflTransGen
      (fun A B : HatLocalTri (boundaryGluingFutureStream W h k) hτ =>
        ∃ d : ℕ × Bool,
          d ∈ triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) A.val ∧
          (d.1, !d.2) ∈
            triangleOrientedDarts (hatCodes (boundaryGluingFutureStream W h k) hτ) B.val ∧
          boundaryGluingHatEdgeMap W h k hτ d.1 ∉ m0GeodesicEdges P) T U := by
    clear hd
    induction hchain with
    | refl => exact .refl
    | @tail A B _ hab ih =>
      apply Relation.ReflTransGen.tail ih
      obtain ⟨e, heA, heB, he⟩ := hab
      refine ⟨e, heA, heB, ?_⟩
      rintro ⟨j, hj⟩
      apply he
      exact ⟨j, boundaryGluingHatEdgeMap_injective W h k hτ ((hid j).symm.trans hj)⟩
  obtain ⟨F, hFR, hF⟩ := boundaryGluing_hatTriangle_gluedFace W h k hτ H hp hfin T
  obtain ⟨F', hF'R, hF'⟩ := boundaryGluing_hatTriangle_gluedFace W h k hτ H hp hfin U
  have hseedF := hF _ hseed
  have hseedF' : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (m0GeodesicSeam P i)) F := by
    change (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (P.codePath.edge i, false)) F
    rw [hid i]
    exact hseedF
  have hFL := boundaryGluing_forward_seam_face_left W h k longest hp P i F hFR hseedF'
  have hF'L := (boundaryGluing_hatTriangle_dualChain_side_iff W h k hτ
    longest hp P hfin hchain' F F' hFR hF'R hF hF' .left).mp hFL
  by_cases he : boundaryGluingHatEdgeMap W h k hτ d.1 ∈ m0GeodesicEdges P
  · exact (m0GeodesicEdges_subset_both hp P he).1
  · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P he
      d.2 F' hF'R (hF' d hd) .left).mpr hF'L

/-- Helper toward Lemma 5.5: a hatted vertex lies on the actual glued
geodesic exactly when it is a vertex of the hatted geodesic. Gluing cannot
introduce a new intersection at a vertex. -/
theorem boundaryGluing_hatVertex_mem_trace_iff
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath) (a : ℕ) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (boundaryGluingHatVertexMap W h k hτ a)) ∈
        m0GeodesicTrace hp P ↔
      a ∈ Set.range (fun i => ((sourceAncestorPath
        (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime
        ⟨boundaryFutureHattedPath k W, hqMode⟩).initial i).1.id) := by
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  let ψ := boundaryGluingHatVertexMap W h k hτ
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  have hv (i : ℕ) : ψ (Q.initial i).1.id = (P.codePath.initial i).1.id := by
    have he := (boundaryGluing_hat_edge_endpoints W h k hτ (Q.edge i)).1
    have hq := (congrArg (fun z => edgeWest z (Q.edge i))
      (boundaryGluing_decoded_stream W h k hτ)).symm.trans
        (Q.edge_outgoing_at_initial _ i).2
    rw [hq, ← hid i] at he
    exact he.symm.trans (P.codePath.edge_outgoing_at_initial _ i).2
  rw [m0Geodesic_pos_mem_trace_iff hp P]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, boundaryGluingHatVertexMap_injective W h k hτ ((hv i).trans hi)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, (hv i).symm⟩

/-- Helper toward Lemma 5.5: every present hatted left edge whose west
endpoint already belongs to the actual closed left side belongs to that
side. At seam vertices this uses the proved angular departure criterion;
away from the seam it uses connected-component transport. -/
theorem boundaryGluing_hat_left_of_west_mem_left
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (e : ℕ)
    (he : EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e)
    (hs : boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingLeftHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode)
    (hw : edgeWest (shiftedStream W 0) (boundaryGluingHatEdgeMap W h k hτ e) ∈
      (m0GeodesicSide hp P .left).vertices) :
    boundaryGluingHatEdgeMap W h k hτ e ∈ (m0GeodesicSide hp P .left).edges := by
  let φ := boundaryGluingHatEdgeMap W h k hτ
  let ψ := boundaryGluingHatVertexMap W h k hτ
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  by_cases hoff : φ e ∈ m0GeodesicEdges P
  · exact (m0GeodesicEdges_subset_both hp P hoff).1
  · have heoff (i : ℕ) : e ≠ Q.edge i := by
      intro hi
      exact hoff ⟨i, (hid i).trans (congrArg φ hi.symm)⟩
    let p := G.pos (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) (φ e)))
    have hpstart : p ∈ (G.arc (wholePlaneDartι W 0 (φ e, false))).image := by
      exact Or.inl (G.arc_start (wholePlaneDartι W 0 (φ e, false))).symm
    by_cases hpP : p ∈ m0GeodesicTrace hp P
    · have hew : edgeWest (shiftedStream W 0) (φ e) = ψ (edgeWest z e) := by
        have hh := (boundaryGluing_hat_edge_endpoints W h k hτ e).1
        rw [← boundaryGluing_decoded_stream W h k hτ] at hh
        exact hh
      have hpP' : G.pos (wholePlaneVertexι W 0 (ψ (edgeWest z e))) ∈
          m0GeodesicTrace hp P := hew ▸ hpP
      obtain ⟨i, hi⟩ := (boundaryGluing_hatVertex_mem_trace_iff W h k hτ
        longest hp P hqMode Tpath hfin hleft (edgeWest z e)).mp hpP'
      exact boundaryGluing_hat_left_seam_departure W h k hτ longest hp P
        hqMode Tpath hfin hleft e i he hi.symm heoff hs
    · have hw' : p ∈ m0GeodesicSideRegion hp P .left := hw
      have hpL := m0GeodesicLeftOpen_closure_inter_complement_subset hp P
        ⟨hw'.1, hw'.2, hpP⟩
      exact (boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P
        hoff hpstart hpP).1.mpr hpL

/-- Helper toward Lemma 5.5: every dart of a finite hatted left path-cut
half maps into the actual glued left side. Directed source reachability in
the finite half propagates the seam-departure seed to all its vertices. -/
theorem boundaryGluing_finiteCut_left_edges
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (t : ℕ) {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B (if longest then XDP.ldp else XDP.sdp) = m)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) t))
    (hprefix : ((selectedGeodesicOfLen R.B
      (if longest then XDP.ldp else XDP.sdp) hR).darts.map I.toEquiv).map
        (fun d => d.1.val) = List.ofFn (fun j : Fin m =>
          (sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime
            ⟨boundaryFutureHattedPath k W, hqMode⟩).edge j.val))
    (d : Fin (ancestorPosHalfRep R hR .left).dartCount) :
    boundaryGluingHatEdgeMap W h k hτ
      (ancestorPosDartId _ t R hR I .left d).1 ∈ (m0GeodesicSide hp P .left).edges := by
  classical
  let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  let B := (ancestorPosHalfRep R hR .left).B
  let f := ancestorPosDartId z t R hR I .left
  let F := ancestorPosVertexId z t R hR I .left
  let φ := boundaryGluingHatEdgeMap W h k hτ
  let ψ := boundaryGluingHatVertexMap W h k hτ
  have hside (c : Fin (ancestorPosHalfRep R hR .left).dartCount) :
      φ (f c).1 ∈ boundaryGluingLeftHatEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode := by
    apply (boundaryGluing_hatSideEdges_iff_finiteCut W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode t R hR I hprefix
      .left (ancestorPosDartMap R hR .left c)).mpr
    have hh : ancestorPosDartMap R hR .left c ∈
        Set.range (ancestorPosDartMap R hR .left) := ⟨c, rfl⟩
    rw [ancestorPosDartMap_range] at hh
    exact hh
  have hend (c : Fin (ancestorPosHalfRep R hR .left).dartCount) (ht : B.map.tail c) :
      edgeWest (shiftedStream W 0) (φ (f c).1) = ψ (F (dartTailVertex B.map c)) ∧
      edgeEast (shiftedStream W 0) (φ (f c).1) = ψ (F (dartHeadVertex B.map c)) := by
    have ho := (ancestorPos_ids_oriented z t R hR I .left c).mp ht
    have he := ancestorPos_ids_endpoints z t R hR I .left c
    rw [ho.2] at he
    have hg := boundaryGluing_hat_edge_endpoints W h k hτ (f c).1
    rw [← boundaryGluing_decoded_stream W h k hτ] at hg
    exact ⟨hg.1.trans (congrArg ψ he.1.symm),
      hg.2.trans (congrArg ψ he.2.symm)⟩
  have hforward (c : Fin (ancestorPosHalfRep R hR .left).dartCount)
      (ht : B.map.tail c)
      (hv : ψ (F (dartTailVertex B.map c)) ∈ (m0GeodesicSide hp P .left).vertices) :
      φ (f c).1 ∈ (m0GeodesicSide hp P .left).edges := by
    apply boundaryGluing_hat_left_of_west_mem_left W h k hτ longest hp P
      hqMode Tpath hfin hleft (f c).1
      ((ancestorPos_ids_oriented z t R hR I .left c).mp ht).1 (hside c)
    rw [(hend c ht).1]
    exact hv
  have hroot : ψ (F B.source) ∈ (m0GeodesicSide hp P .left).vertices := by
    have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
      hp Tpath P hfin hleft
    have he := (boundaryGluing_hat_edge_endpoints W h k hτ (Q.edge 0)).1
    have hq : edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) (Q.edge 0) = 0 :=
      (congrArg (fun w => edgeWest w (Q.edge 0))
        (boundaryGluing_decoded_stream W h k hτ)).symm.trans Q.first_edge_outgoing.2
    rw [hq, ← hid 0] at he
    have hsource : F B.source = 0 :=
      ancestorPos_source_id_of_prefix z Q t R hR I hprefix .left
    have he' : edgeWest (shiftedStream W 0) (P.codePath.edge 0) = ψ 0 := he
    rw [hsource, ← he']
    exact (m0GeodesicSide_endpoints hp P .left _
      (m0GeodesicEdges_subset_both hp P (m0GeodesicSeam_mem_edges P 0)).1).1
  have hvertex (v : MapVertex B.map) : ψ (F v) ∈ (m0GeodesicSide hp P .left).vertices := by
    obtain ⟨j, A, _⟩ := exists_simple_source_pathBase B v
    have hreach : Relation.ReflTransGen B.map.directedStep B.source v := by
      have hr (i : ℕ) (hi : i ≤ j) : Relation.ReflTransGen B.map.directedStep
          (A.vertices.get ⟨0, by rw [A.vertices_length]; omega⟩)
          (A.vertices.get ⟨i, by rw [A.vertices_length]; omega⟩) := by
        induction i with
        | zero => exact .refl
        | succ i ih =>
          have hs := A.edge_step ⟨i, by rw [A.darts_length]; omega⟩
          exact (ih (by omega)).tail ⟨_, hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩
      simpa only [A.start_vertex, A.end_vertex] using hr j le_rfl
    clear A
    induction hreach with
    | refl => exact hroot
    | @tail b c _ hbc ih =>
      obtain ⟨a, _, ht, hb, hc⟩ := hbc
      change dartTailVertex B.map a = b at hb
      change dartHeadVertex B.map a = c at hc
      have ha := hforward a ht (by rw [hb]; exact ih)
      have hh := (m0GeodesicSide_endpoints hp P .left _ ha).2
      change edgeEast (shiftedStream W 0) (φ (f a).1) ∈ _ at hh
      rw [(hend a ht).2, hc] at hh
      exact hh
  by_cases ht : B.map.tail d
  · exact hforward d ht (hvertex _)
  · have ht' : B.map.tail (B.map.edgeInv d) := by
      by_contra hn
      exact ht ((B.map.tail_iff d (B.noMissingDarts d)).mpr hn)
    have hh := hforward (B.map.edgeInv d) ht' (hvertex _)
    have he := congrArg Prod.fst (ancestorPos_ids_opposite z t R hR I .left d)
    exact he ▸ hh




theorem boundaryGluingLeftHatEdges_subset_left
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath) :
    boundaryGluingLeftHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode ⊆
        (m0GeodesicSide hp P .left).edges := by
  rintro e ⟨a, ha, rfl⟩
  have hs : boundaryGluingHatEdgeMap W h k hτ a ∈ boundaryGluingHatSideEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode .left := ⟨a, ha, rfl⟩
  obtain ⟨t, ℓ, r, n, m, R, hR, I, hprefix, d, hd, hleftHalf⟩ :=
    (boundaryGluing_hatSideEdges_iff_exists_finiteCut W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode .left a).mp hs
  have hrange : d ∈ Set.range (ancestorPosDartMap R hR .left) := by
    rw [ancestorPosDartMap_range]
    exact hleftHalf
  obtain ⟨c, rfl⟩ := hrange
  have hh := boundaryGluing_finiteCut_left_edges W h k hτ longest hp P
    hqMode Tpath hfin hleft t R hR I hprefix c
  change boundaryGluingHatEdgeMap W h k hτ (I.toEquiv
    (ancestorPosDartMap R hR .left c)).1.val ∈ _ at hh
  rw [hd] at hh
  exact hh




theorem boundaryGluingBetaEdges_subset_left
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath) :
    boundaryGluingBetaEdges W h k hτ ⊆ (m0GeodesicSide hp P .left).edges :=
  (boundaryGluingBetaEdges_subset_leftHatEdges W h k hτ
    (if longest then XDP.ldp else XDP.sdp) hqMode).trans
      (boundaryGluingLeftHatEdges_subset_left W h k hτ longest hp P
        hqMode Tpath hfin hleft)

/-- Helper toward Lemma 5.5: the geometric future vertex embedding. -/
@[expose] noncomputable def boundaryGluingFutureVertexMap : ℕ → ℕ :=
  limitVertexMap (kmswShiftVertexMapAll (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)) (boundaryGluingFutureStream W h k)

/-- Helper toward Lemma 5.5: the future embedding preserves both endpoints
of every geometric edge, without requiring directed presence. -/
theorem boundaryGluing_future_edge_endpoints (e : ℕ) :
    edgeWest (shiftedStream W 0) (boundaryGluingEdgeMap W h k e) =
      boundaryGluingFutureVertexMap W h k (edgeWest (boundaryGluingFutureStream W h k) e) ∧
    edgeEast (shiftedStream W 0) (boundaryGluingEdgeMap W h k e) =
      boundaryGluingFutureVertexMap W h k (edgeEast (boundaryGluingFutureStream W h k) e) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  have he := kmsw_edge_allocated_by_self u e
  have S := (kmswShift_sim2_all w t e).sim
  have hW := edge_endpoints_eq w (S.edge_bound e he)
  have hU := edge_endpoints_eq u he
  have hi := S.incidence e he
  have hb := kmswStage_endpoints_lt_nextVertex u e e he
  have hvW := limitVertexMap_eq_of_allocated (kmswShiftVertexMapAll w t)
    (kmswShiftVertexMapAll_extend w t) e _ hb.1
  have hvE := limitVertexMap_eq_of_allocated (kmswShiftVertexMapAll w t)
    (kmswShiftVertexMapAll_extend w t) e _ hb.2
  rw [boundaryGluingEdgeMap_eq_shift W h k]
  change edgeWest w (kmswShiftEdgeMapAll w t e e) = _ ∧
    edgeEast w (kmswShiftEdgeMapAll w t e e) = _
  constructor
  · rw [← hW.1, hi.1, ← hU.1]
    exact hvW.symm
  · rw [← hW.2, hi.2, ← hU.2]
    exact hvE.symm

/-- Helper toward Lemma 5.5: future vertices remain distinct after gluing. -/
theorem boundaryGluingFutureVertexMap_injective :
    Function.Injective (boundaryGluingFutureVertexMap W h k) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  intro a b hab
  obtain ⟨m, hm⟩ := kmswVertexAllocated_all u ⟨a⟩
  obtain ⟨n, hn⟩ := kmswVertexAllocated_all u ⟨b⟩
  have ha := hm.trans_le (CutConverse.nextVertex_mono u (Nat.le_max_left m n))
  have hb := hn.trans_le (CutConverse.nextVertex_mono u (Nat.le_max_right m n))
  have hma := limitVertexMap_eq_of_allocated (kmswShiftVertexMapAll w t)
    (kmswShiftVertexMapAll_extend w t) (max m n) a ha
  have hmb := limitVertexMap_eq_of_allocated (kmswShiftVertexMapAll w t)
    (kmswShiftVertexMapAll_extend w t) (max m n) b hb
  change limitVertexMap (kmswShiftVertexMapAll w t) u a =
    limitVertexMap (kmswShiftVertexMapAll w t) u b at hab
  change limitVertexMap (kmswShiftVertexMapAll w t) u a = _ at hma
  change limitVertexMap (kmswShiftVertexMapAll w t) u b = _ at hmb
  rw [hma, hmb] at hab
  exact (kmswShift_sim2_all w t (max m n)).sim.vertex_injective a b ha hb hab

/-- Helper toward Lemma 5.5: a future vertex unreachable from its root
cannot become a vertex or interior point of the actual geodesic. -/
theorem boundaryGluing_unreachable_vertex_not_mem_trace
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (v : ℕ) (hv : ¬ MhatVertex (boundaryGluingFutureStream W h k) v) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (boundaryGluingFutureVertexMap W h k v)) ∉
        m0GeodesicTrace hp P := by
  let u := boundaryGluingFutureStream W h k
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  intro htrace
  obtain ⟨i, hi⟩ := (m0Geodesic_pos_mem_trace_iff hp P _).mp htrace
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  have he := (boundaryGluing_hat_edge_endpoints W h k hτ (Q.edge i)).1
  have hq := (congrArg (fun z => edgeWest z (Q.edge i))
    (boundaryGluing_decoded_stream W h k hτ)).symm.trans
      (Q.edge_outgoing_at_initial _ i).2
  rw [hq, ← hid i, (P.codePath.edge_outgoing_at_initial _ i).2] at he
  change (P.codePath.initial i).1.id = boundaryGluingFutureVertexMap W h k v at hi
  have hvEq : v = hatLimitVertexMap u hτ (Q.initial i).1.id :=
    boundaryGluingFutureVertexMap_injective W h k (hi.symm.trans he)
  apply hv
  rw [hvEq]
  exact alloc_reachable (hatLimitExplicitInput u hτ)
    (kmswVertexAllocated_all (hatCodes u hτ) ⟨(Q.initial i).1.id⟩)

/-- Helper toward Lemma 5.5: every ambient point strictly west of the
geodesic root belongs to the component based west of that root. -/
theorem boundaryGluing_west_of_root_mem_leftOpen {z : ℂ}
    (hz : z ∈ m0GeodesicAmbientRegion W H h)
    (hx : z.re < seamX (shiftedStream W 0) h (H.1 0) k) :
    z ∈ m0GeodesicLeftOpen hp P := by
  let f := seamFun (shiftedStream W 0) h (H.1 0)
  let a := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  let x₀ := seamX (shiftedStream W 0) h (H.1 0) k
  have ha : a < x₀ := seamX_strictMono (shiftedStream W 0) h (H.1 0) (by omega)
  have hf := seamFun_continuous (shiftedStream W 0) h (H.1 0)
  have hbase : (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x (k - 1)) = (⟨a, f a⟩ : ℂ) := by
    rw [(m0CutData W H h hLL).x_eq h hLL (k - 1), m0Geodesic_pos_runZero hp]
    exact boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) (k - 1)
  obtain ⟨X, g, _, _, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp P
  let V : Set ℂ := (fun y : ℝ => (⟨z.re, y⟩ : ℂ)) '' Set.Icc (f z.re) z.im
  let T := graphOver (min a z.re) (max a z.re) f ∪ V
  have hV : IsPreconnected V :=
    isPreconnected_Icc.image (fun y : ℝ => (⟨z.re, y⟩ : ℂ)) (by
      simp only [Complex.mk_eq_add_mul_I]
      fun_prop)
  have hT : IsPreconnected T :=
    IsPreconnected.union'
      ⟨⟨z.re, f z.re⟩, ⟨min_le_right _ _, le_max_right _ _, rfl⟩,
        ⟨f z.re, ⟨le_rfl, hz⟩, rfl⟩⟩
      (isPathConnected_graphOver min_le_max hf.continuousOn).isConnected.isPreconnected hV
  have hsub : T ⊆ m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp P := by
    rintro q (hq | hq)
    · refine ⟨?_, ?_⟩
      · change f q.re ≤ q.im
        exact hq.2.2.symm.le
      · intro hqP
        rw [hgraph] at hqP
        have hlt : q.re < x₀ := hq.2.1.trans_lt (max_lt ha hx)
        exact (not_le_of_gt hlt) hqP.1.1
    · obtain ⟨y, hy, rfl⟩ := hq
      refine ⟨hy.1, ?_⟩
      intro hqP
      rw [hgraph] at hqP
      exact (not_le_of_gt hx) hqP.1.1
  have hb : (⟨a, f a⟩ : ℂ) ∈ T :=
    Or.inl ⟨min_le_left _ _, le_max_left _ _, rfl⟩
  have hzT : z ∈ T := by
    right
    exact ⟨z.im, ⟨hz, le_rfl⟩, Complex.eta z⟩
  unfold m0GeodesicLeftOpen
  rw [hbase]
  exact hT.subset_connectedComponentIn hb hsub hzT

/-- Helper toward Lemma 5.5: the future root is the prescribed hit-indexed
boundary vertex in run zero. -/
theorem boundaryGluingFutureVertexMap_zero :
    boundaryGluingFutureVertexMap W h k 0 =
      boundaryVertex (shiftedStream W 0) h k := by
  have hv : boundaryGluingFutureVertexMap W h k 0 =
      kmswShiftVertexMapAll (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k) 0 0 :=
    limitVertexMap_eq_of_allocated _
      (kmswShiftVertexMapAll_extend (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)) 0 0 (by change 0 < 2; omega)
  exact hv.trans (kmswShift_root_vertex_map _ h k)

/-- Helper toward Lemma 5.5: geometric edges point strictly east in the
actual drawing, including missing boundary edges. -/
theorem boundaryGluing_edge_re_lt (e : ℕ) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) e))).re <
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (edgeEast (shiftedStream W 0) e))).re := by
  rw [m0Geodesic_pos_runZero hp, m0Geodesic_pos_runZero hp]
  let w := shiftedStream W 0
  have he := kmsw_edge_allocated_by_self w e
  have hv := kmswStage_endpoints_lt_nextVertex w e e he
  have hend := edge_endpoints_eq w he
  have hpos (v : ℕ) (hv : v < (kmswStage w e).nextVertex) :
      (monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)).pos v =
        layoutPos w e v := monotoneLimitDrawing_pos_layout w (H.1 0) _ e v hv
  rw [← hend.1, ← hend.2, hpos _ hv.1, hpos _ hv.2]
  change (kmswStageRank w e ((kmswStage w e).west e) : ℝ) <
    (kmswStageRank w e ((kmswStage w e).east e) : ℝ)
  exact_mod_cast kmswStageRank_strict w e e he

/-- Helper toward Lemma 5.5: every strictly negative future boundary
vertex is a left seed, even when its adjacent geometric edges are missing. -/
theorem boundaryGluing_future_negative_boundary_mem_leftOpen
    (hb : BoundaryHitWitnesses (boundaryGluingFutureStream W h k))
    {j : ℤ} (hj : j < 0) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (boundaryGluingFutureVertexMap W h k
        (boundaryVertex (boundaryGluingFutureStream W h k) hb j))) ∈
          m0GeodesicLeftOpen hp P := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let u := boundaryGluingFutureStream W h k
  let ψ := boundaryGluingFutureVertexMap W h k
  have hmono : StrictMono (fun j : ℤ =>
      (G.pos (wholePlaneVertexι W 0 (ψ (boundaryVertex u hb j)))).re) := by
    apply strictMono_int_of_lt_succ
    intro i
    have he := boundaryGluing_edge_re_lt W h (H := H) hp
      (boundaryGluingEdgeMap W h k (boundaryOuterEdge u hb i))
    have hh := boundaryGluing_future_edge_endpoints W h k (boundaryOuterEdge u hb i)
    rw [(boundaryOuterEdge_endpoints u hb i).1] at hh
    rw [(boundaryOuterEdge_endpoints u hb i).2.1] at hh
    rw [hh.1, hh.2] at he
    exact he
  apply boundaryGluing_west_of_root_mem_leftOpen W h k longest hp P
    (m0Geodesic_pos_mem_ambient hp _)
  have hlt := hmono hj
  dsimp only at hlt
  change (G.pos (wholePlaneVertexι W 0 (ψ (boundaryVertex u hb j)))).re <
    (G.pos (wholePlaneVertexι W 0 (ψ (boundaryVertex u hb 0)))).re at hlt
  dsimp only [ψ, G] at hlt
  rw [boundaryVertex_zero, boundaryGluingFutureVertexMap_zero W h k] at hlt
  have hroot : (G.pos (wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k))).re =
      seamX (shiftedStream W 0) h (H.1 0) k := by
    rw [m0Geodesic_pos_runZero hp]
    rfl
  exact hlt.trans_eq hroot

open Quiver

/-- Helper toward Lemma 5.5; not a paper result.
Reachability propagates across a present stage edge. -/
private theorem gluing_reachable_across_stage_edge (w : ℕ → Fin 3) (n e u : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present e = true)
    (hr : Reachable (⟨u⟩ : PresentVertex w) ⟨(kmswStage w n).west e⟩) :
    Reachable (⟨u⟩ : PresentVertex w) ⟨(kmswStage w n).east e⟩ := by
  obtain ⟨p⟩ := hr
  have hends := edge_endpoints_eq w he
  exact ⟨p.cons ⟨e, ⟨n, he, hp⟩, hends.1.symm, hends.2.symm⟩⟩

/-- Helper toward Lemma 5.5; not a paper result.
Every allocated vertex is reached from a nonpositive-index outer-boundary vertex.
The path uses only present edges, including when its source borders missing edges. -/
private theorem gluing_stageVertex_reachable_from_leftBoundary (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    ∃ k : ℤ, k ≤ 0 ∧ Reachable (⟨boundaryVertex w hb k⟩ : PresentVertex w) ⟨v⟩ := by
  induction n generalizing v with
  | zero =>
    have hv' : v < 2 := hv
    refine ⟨0, le_rfl, ?_⟩
    rw [boundaryVertex_zero]
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · exact Reachable.refl _
    · exact gluing_reachable_across_stage_edge w 0 0 0 (by change 0 < 1; omega) rfl
        (Reachable.refl _)
  | succ n ih =>
    have hend := kmswStage_endpoints_lt_nextVertex w n (act w n)
      (act_lt_nextEdge w le_rfl)
    by_cases hold : v < (kmswStage w n).nextVertex
    · exact ih v hold
    by_cases h0 : w n = 0
    · cases hs : (kmswStage w n).UL.dropLast.reverse with
      | cons e es =>
        simp only [kmswStage, kmswStep, kmswCodeStep, h0, ite_true,
          kmswStepOfStep, hs, State.addEdge] at hv
        exact (hold hv).elim
      | nil =>
        have hvnew : v = (kmswStage w n).nextVertex := by
          simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
            hs, State.addEdge] at hv
          omega
        have hmem : (kmswStage w n).nextEdge + 1 ∈ (kmswStage w (n + 1)).LL := by
          simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep, hs]
        have hw : (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1) = v := by
          simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
            hs, State.addEdge, hvnew]
        obtain ⟨k, hk⟩ := boundaryVertex_covers_lowerBoundary w hb v
          ⟨n + 1, _, Or.inl hmem, Or.inl hw⟩
        by_cases hkpos : 1 ≤ k
        · refine ⟨0, le_rfl, ?_⟩
          rw [← hk]
          exact boundaryVertex_nonneg_reachable w hb le_rfl (by omega)
        · exact ⟨k, by omega, hk ▸ Reachable.refl _⟩
    · by_cases h1 : w n = 1
      · have hvnew : v = (kmswStage w n).nextVertex := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
            State.addEdge] at hv
          omega
        subst v
        have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
        have hp : (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
        obtain ⟨k, hk, hr⟩ := ih _ hend.1
        have hreach := gluing_reachable_across_stage_edge w (n + 1)
          (kmswStage w n).nextEdge (boundaryVertex w hb k) he hp
        have hw : (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
            (kmswStage w n).west (act w n) := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge, act]
        have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
            (kmswStage w n).nextVertex := by
          simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
        rw [hw, ht] at hreach
        exact ⟨k, hk, hreach hr⟩
      · cases hs : (kmswStage w n).UR with
        | cons e es =>
          simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ite_false,
            kmswStepOfStep, hs] at hv
          exact (hold hv).elim
        | nil =>
          have hvnew : v = (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge] at hv
            omega
          subst v
          have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge]
          have hp : (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge]
          obtain ⟨k, hk, hr⟩ := ih _ hend.2
          have hreach := gluing_reachable_across_stage_edge w (n + 1)
            (kmswStage w n).nextEdge (boundaryVertex w hb k) he hp
          have hw : (kmswStage w (n + 1)).west (kmswStage w n).nextEdge =
              (kmswStage w n).east (act w n) := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge, act]
          have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge =
              (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
              hs, State.addEdge]
          rw [hw, ht] at hreach
          exact ⟨k, hk, hreach hr⟩


/-- Helper toward Lemma 5.5: the last point of a polyline belongs to its
full geometric image. -/
private theorem gluing_finish_mem_image (p : Polyline) : p.finish ∈ p.image := by
  rw [← p.point_last_eq_finish]
  by_cases hlen : 2 ≤ p.points.length
  · refine Or.inr ⟨p.points.length - 2, by omega, ?_⟩
    rw [Polyline.segmentAt,
      show p.points.length - 2 + 1 = p.points.length - 1 by omega]
    exact right_mem_segment ℝ _ _
  · have hlen1 : p.points.length = 1 := by
      have := List.length_pos_iff.mpr p.nonempty
      omega
    simp only [hlen1, Nat.sub_self, Polyline.point_zero_eq_start]
    exact Or.inl rfl

/-- Helper toward Lemma 5.5: a directed future path ending at an unreachable
vertex propagates its negative-boundary left seed without meeting the trace. -/
theorem boundaryGluing_future_path_unreachable_mem_leftOpen
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hb : BoundaryHitWitnesses (boundaryGluingFutureStream W h k))
    {j : ℤ} (hj : j < 0) {v : PresentVertex (boundaryGluingFutureStream W h k)}
    (p : Quiver.Path (⟨boundaryVertex (boundaryGluingFutureStream W h k) hb j⟩) v)
    (hv : ¬ MhatVertex (boundaryGluingFutureStream W h k) v.id) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (boundaryGluingFutureVertexMap W h k v.id)) ∈
        m0GeodesicLeftOpen hp P := by
  let u := boundaryGluingFutureStream W h k
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let ψ := boundaryGluingFutureVertexMap W h k
  have havoid (v : ℕ) (hv : ¬ MhatVertex u v) :
      G.pos (wholePlaneVertexι W 0 (ψ v)) ∉ m0GeodesicTrace hp P :=
    boundaryGluing_unreachable_vertex_not_mem_trace W h k longest hp P
      hτ hqMode Tpath hfin hleft v hv
  induction p with
  | nil => exact boundaryGluing_future_negative_boundary_mem_leftOpen W h k longest hp P hb hj
  | @cons b c p e ih =>
    have hbnot : ¬ MhatVertex u b.id := fun hr => hv (hr.trans e.toPath.reachable)
    have hbL := ih hbnot
    let E := boundaryGluingEdgeMap W h k e.val
    have hend := boundaryGluing_future_edge_endpoints W h k e.val
    have hw : edgeWest (shiftedStream W 0) E = ψ b.id :=
      hend.1.trans (congrArg ψ e.property.2.1)
    have ht : edgeEast (shiftedStream W 0) E = ψ c.id :=
      hend.2.trans (congrArg ψ e.property.2.2)
    have hoff : E ∉ m0GeodesicEdges P := by
      rintro ⟨i, hi⟩
      apply havoid b.id hbnot
      rw [← hw, ← hi, (P.codePath.edge_outgoing_at_initial _ i).2]
      exact m0Geodesic_initial_pos_mem_trace hp P i
    have hqb : G.pos (wholePlaneVertexι W 0 (ψ b.id)) ∈
        (G.arc (wholePlaneDartι W 0 (E, false))).image := by
      have hs := G.arc_start (wholePlaneDartι W 0 (E, false))
      change (G.arc (wholePlaneDartι W 0 (E, false))).start =
        G.pos (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) E)) at hs
      rw [hw] at hs
      exact Or.inl hs.symm
    have hqc : G.pos (wholePlaneVertexι W 0 (ψ c.id)) ∈
        (G.arc (wholePlaneDartι W 0 (E, false))).image := by
      have hs := G.arc_finish (wholePlaneDartι W 0 (E, false))
      change (G.arc (wholePlaneDartι W 0 (E, false))).finish =
        G.pos (wholePlaneVertexι W 0 (edgeEast (shiftedStream W 0) E)) at hs
      rw [ht] at hs
      rw [← hs]
      exact gluing_finish_mem_image _
    have heL := (boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P
      hoff hqb (havoid b.id hbnot)).1.mpr hbL
    exact (boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P
      hoff hqc (havoid c.id hv)).1.mp heL

/-- Helper toward Lemma 5.5: every future vertex outside the root-reachable
carrier lies in the actual open left side. -/
theorem boundaryGluing_unreachable_vertex_mem_leftOpen
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (v : ℕ) (hv : ¬ MhatVertex (boundaryGluingFutureStream W h k) v) :
    (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (boundaryGluingFutureVertexMap W h k v)) ∈
        m0GeodesicLeftOpen hp P := by
  let u := boundaryGluingFutureStream W h k
  let hb := hatBoundaryHitWitnesses u hτ
  obtain ⟨n, hn⟩ := kmswVertexAllocated_all u ⟨v⟩
  obtain ⟨j, hj, p⟩ := gluing_stageVertex_reachable_from_leftBoundary u hb n v hn
  have hjlt : j < 0 := by
    by_contra hnot
    have hj0 : j = 0 := by omega
    subst j
    rw [boundaryVertex_zero] at p
    exact hv p
  obtain ⟨p⟩ := p
  exact boundaryGluing_future_path_unreachable_mem_leftOpen W h k longest hp P
    hτ hqMode Tpath hfin hleft hb hjlt p hv

/-- Helper toward Lemma 5.5: an edge with an unreachable future endpoint
belongs to the actual left side; no orientation of that edge is required. -/
theorem boundaryGluing_future_edge_left_of_unreachable_endpoint
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (e : ℕ)
    (he : ¬ MhatVertex (boundaryGluingFutureStream W h k)
      (edgeWest (boundaryGluingFutureStream W h k) e) ∨
      ¬ MhatVertex (boundaryGluingFutureStream W h k)
        (edgeEast (boundaryGluingFutureStream W h k) e)) :
    boundaryGluingEdgeMap W h k e ∈ (m0GeodesicSide hp P .left).edges := by
  let u := boundaryGluingFutureStream W h k
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let E := boundaryGluingEdgeMap W h k e
  let ψ := boundaryGluingFutureVertexMap W h k
  have hend := boundaryGluing_future_edge_endpoints W h k e
  obtain ⟨v, hv, hve⟩ : ∃ v, ¬ MhatVertex u v ∧
      (edgeWest (shiftedStream W 0) E = ψ v ∨
        edgeEast (shiftedStream W 0) E = ψ v) := by
    rcases he with hw | ht
    · exact ⟨edgeWest u e, hw, Or.inl hend.1⟩
    · exact ⟨edgeEast u e, ht, Or.inr hend.2⟩
  have hvnot := boundaryGluing_unreachable_vertex_not_mem_trace W h k longest hp P
    hτ hqMode Tpath hfin hleft v hv
  have hvL := boundaryGluing_unreachable_vertex_mem_leftOpen W h k longest hp P
    hτ hqMode Tpath hfin hleft v hv
  have hoff : E ∉ m0GeodesicEdges P := by
    rintro ⟨i, hi⟩
    apply hvnot
    change G.pos (wholePlaneVertexι W 0 (ψ v)) ∈ m0GeodesicTrace hp P
    rcases hve with hw | ht
    · rw [← hw, ← hi, (P.codePath.edge_outgoing_at_initial _ i).2]
      exact m0Geodesic_initial_pos_mem_trace hp P i
    · rw [← ht, ← hi, (P.codePath.edge_incoming_at_succ _ i).2]
      exact m0Geodesic_initial_pos_mem_trace hp P (i + 1)
  have hvArc : G.pos (wholePlaneVertexι W 0 (ψ v)) ∈
      (G.arc (wholePlaneDartι W 0 (E, false))).image := by
    rcases hve with hw | ht
    · rw [← hw]
      exact Or.inl (G.arc_start (wholePlaneDartι W 0 (E, false))).symm
    · have hs := G.arc_finish (wholePlaneDartι W 0 (E, false))
      change (G.arc (wholePlaneDartι W 0 (E, false))).finish =
        G.pos (wholePlaneVertexι W 0 (edgeEast (shiftedStream W 0) E)) at hs
      rw [← ht, ← hs]
      exact gluing_finish_mem_image _
  exact (boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P
    hoff hvArc hvnot).1.mpr hvL




theorem boundaryGluingPrimedEdges_subset_left
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath) :
    boundaryGluingPrimedEdges W h k hτ ⊆ (m0GeodesicSide hp P .left).edges := by
  classical
  rintro E ⟨a, rfl⟩
  let u := boundaryGluingFutureStream W h k
  let hb := hatBoundaryHitWitnesses u hτ
  let e := primedLimitEdgeMap u hτ a
  have hg : primeGeomEdge u hfin hb e :=
    (primeGeomEdge_iff_primedLimitEdge u hfin hb hτ e).mpr ⟨a, rfl⟩
  change boundaryGluingEdgeMap W h k e ∈ _
  rcases hg with hnot | hbeta
  · apply boundaryGluing_future_edge_left_of_unreachable_endpoint W h k longest hp P
      hτ hqMode Tpath hfin hleft e
    exact not_and_or.mp hnot
  · obtain ⟨i, hi⟩ := hbeta
    apply boundaryGluingBetaEdges_subset_left W h k hτ longest hp P
      hqMode Tpath hfin hleft
    refine ⟨i, ?_⟩
    apply congrArg (boundaryGluingEdgeMap W h k)
    exact (hattedLeftBoundaryBeta0EdgeCorrespondence_proved u hτ hfin hb i).trans hi

/-- Helper toward Lemma 5.5: directed paths have nondecreasing real
coordinate in the actual glued drawing. -/
theorem boundaryGluing_path_re_le {a b : PresentVertex (shiftedStream W 0)}
    (p : Quiver.Path a b) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 a.id)).re ≤
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 b.id)).re := by
  induction p with
  | nil => exact le_rfl
  | @cons b c p e ih =>
    have he := boundaryGluing_edge_re_lt W h (H := H) hp e.val
    rw [e.property.2.1, e.property.2.2] at he
    exact ih.trans he.le

/-- Helper toward Lemma 5.5: at a positive boundary hit every prefix
edge other than the active edge has its west endpoint strictly west of x_k. -/
theorem boundaryGluing_prefixMinus_west_lt_root (hk : 0 < k) {e : ℕ}
    (he : e ∈ boundaryGluingPrefixMinusEdges W h k) :
    ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) e))).re <
        seamX (shiftedStream W 0) h (H.1 0) k := by
  classical
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  have hk1 : 1 ≤ k := by omega
  have hfind : t = Nat.find (h.rightHit k hk1) := by
    dsimp [t]
    unfold boundaryHitTime
    simp only [dite_eq_right (ne_of_gt hk), dite_eq_left hk]
  have hspec : R w t = -k := boundaryHitTime_right_spec w h hk1
  have htpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := by omega
    rw [ht0] at hspec
    change 0 = -k at hspec
    omega
  have hmin : R w t = minR w t :=
    (kmswStage_UR_eq_nil_iff_record w t).mp (boundaryHit_right_UR_empty w h hk1)
  have hrec : ∀ j < t, R w t ≤ R w j - 1 := by
    intro j hj
    have hm := runningMin_le (R w) t j hj.le
    change minR w t ≤ R w j at hm
    rw [← hmin] at hm
    have hn := Nat.find_min (h.rightHit k hk1) (show j < Nat.find (h.rightHit k hk1) by
      rw [← hfind]; exact hj)
    change R w j ≠ -k at hn
    omega
  have hd := record_stage_before_empty_UR_public w t hrec htpos
  have hprev : t - 1 + 1 = t := by omega
  have hcount : (kmswStage w t).nextEdge = (kmswStage w (t - 1)).nextEdge + 1 := by
    conv_lhs => rw [← hprev]
    simp only [kmswStage, kmswStep, kmswCodeStep, hd.1,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      ↓reduceIte, kmswStepOfStep, hd.2, State.addEdge]
  have hact : act w t = (kmswStage w (t - 1)).nextEdge := by
    change (kmswStage w t).active = _
    conv_lhs => rw [← hprev]
    simp only [kmswStage, kmswStep, kmswCodeStep, hd.1,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      ↓reduceIte, kmswStepOfStep, hd.2, State.addEdge]
  have heold : e < (kmswStage w (t - 1)).nextEdge := by
    have heb : e < (kmswStage w t).nextEdge := he.1
    have hne : e ≠ act w t := he.2
    omega
  have hend := edge_endpoints_eq w heold
  have hv := (kmswStage_endpoints_lt_nextVertex w (t - 1) e heold).2
  rw [hend.2] at hv
  obtain ⟨p⟩ := allocated_vertex_reaches_strict_record w t hrec htpos (edgeEast w e) hv
  have hle := boundaryGluing_path_re_le W h (H := H) hp p
  have hroot : (recordVertex w t).id = boundaryVertex w h k := by
    change (kmswStage w t).west (act w t) = _
    exact (edge_endpoints_eq w (act_lt_nextEdge w le_rfl)).1.trans
      (boundaryVertex_eq_edgeWest_hit w h k).symm
  rw [hroot] at hle
  have hrootpos : ((WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      (wholePlaneVertexι W 0 (boundaryVertex w h k))).re =
        seamX (shiftedStream W 0) h (H.1 0) k := by
    rw [m0Geodesic_pos_runZero hp]
    rfl
  exact (boundaryGluing_edge_re_lt W h (H := H) hp e).trans_le (hle.trans_eq hrootpos)




theorem boundaryGluingPrefixMinusEdges_subset_left (hk : 0 ≤ k) :
    boundaryGluingPrefixMinusEdges W h k ⊆ (m0GeodesicSide hp P .left).edges := by
  intro e he
  by_cases hk0 : k = 0
  · subst k
    rw [boundaryGluingPrefixMinusEdges_zero] at he
    exact he.elim
  have hx := boundaryGluing_prefixMinus_west_lt_root W h k (H := H) hp (by omega) he
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let q := G.pos (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) e))
  have hqL : q ∈ m0GeodesicLeftOpen hp P :=
    boundaryGluing_west_of_root_mem_leftOpen W h k longest hp P
      (m0Geodesic_pos_mem_ambient hp _) hx
  have hqP : q ∉ m0GeodesicTrace hp P := by
    obtain ⟨X, g, _, _, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp P
    intro hq
    rw [hgraph] at hq
    exact (not_le_of_gt hx) hq.1.1
  have hoff : e ∉ m0GeodesicEdges P := by
    rintro ⟨i, hi⟩
    apply hqP
    dsimp only [q]
    rw [← hi, (P.codePath.edge_outgoing_at_initial _ i).2]
    exact m0Geodesic_initial_pos_mem_trace hp P i
  have hqArc : q ∈ (G.arc (wholePlaneDartι W 0 (e, false))).image :=
    Or.inl (G.arc_start (wholePlaneDartι W 0 (e, false))).symm
  exact (boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P
    hoff hqArc hqP).1.mpr hqL



theorem boundaryGluingPrimedEdges_sdiff_seam_subset_left
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath) :
    boundaryGluingPrimedEdges W h k hτ \
      boundaryGluingHatSeamEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode ⊆
          (m0GeodesicSide hp P .left).edges :=
  Set.sdiff_subset.trans (boundaryGluingPrimedEdges_subset_left W h k hτ
    longest hp P hqMode Tpath hfin hleft)



theorem boundaryGluingPrefixMinusEdges_sdiff_seam_subset_left
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (hk : 0 ≤ k) :
    boundaryGluingPrefixMinusEdges W h k \
      boundaryGluingHatSeamEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode ⊆
          (m0GeodesicSide hp P .left).edges :=
  Set.sdiff_subset.trans (boundaryGluingPrefixMinusEdges_subset_left W h k longest hp P hk)

/-- Helper toward Lemma 5.5: the closed epigraph of a proper graph ray
remains closed when its right endpoint is finite, by height escape. -/
private theorem gluing_graphRay_epigraph_closed
    {x₀ : ℝ} {X : WithTop ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (rayDomain x₀ X))
    (hesc : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ X,
      ∀ t ∈ rayDomain x₀ X, a ≤ t → M ≤ g t) :
    IsClosed {q : ℂ | q.re ∈ rayDomain x₀ X ∧ g q.re ≤ q.im} := by
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hre := (Complex.continuous_re.tendsto z).comp hz
  have him := (Complex.continuous_im.tendsto z).comp hz
  obtain ⟨M, hM⟩ := him.bddAbove_range
  obtain ⟨a, ha, hbig⟩ := hesc (M + 1)
  have hlt : ∀ n, (u n).re < a := by
    intro n
    by_contra hn
    have h₁ := hbig _ (hu n).1 (le_of_not_gt hn)
    have h₂ := (hu n).2
    have h₃ := hM (Set.mem_range_self n)
    change (u n).im ≤ M at h₃
    linarith only [h₁, h₂, h₃]
  have hza : z.re ≤ a := le_of_tendsto' hre (fun n => (hlt n).le)
  have hzx : x₀ ≤ z.re := ge_of_tendsto' hre (fun n => (hu n).1.1)
  have hzd : z.re ∈ rayDomain x₀ X :=
    ⟨hzx, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hza) ha.2⟩
  refine ⟨hzd, ?_⟩
  have hlim := (hg z.re hzd).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr
      ⟨hre, Filter.Eventually.of_forall (fun n => (hu n).1)⟩)
  exact le_of_tendsto_of_tendsto' hlim him (fun n => (hu n).2)

/-- Helper toward Lemma 5.5: the hypograph extended beyond the right
endpoint of a graph ray is closed. -/
private theorem gluing_graphRay_hypograph_closed
    {x₀ : ℝ} {X : WithTop ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (rayDomain x₀ X)) :
    IsClosed {q : ℂ | x₀ ≤ q.re ∧
      (q.re ∈ rayDomain x₀ X → q.im ≤ g q.re)} := by
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hre := (Complex.continuous_re.tendsto z).comp hz
  have him := (Complex.continuous_im.tendsto z).comp hz
  refine ⟨ge_of_tendsto' hre (fun n => (hu n).1), ?_⟩
  intro hzd
  have hev : ∀ᶠ n in Filter.atTop, (u n).re ∈ rayDomain x₀ X := by
    induction X using WithTop.recTopCoe with
    | top =>
      exact Filter.Eventually.of_forall (fun n => ⟨(hu n).1, WithTop.coe_lt_top _⟩)
    | coe b =>
      have hzb : z.re < b := WithTop.coe_lt_coe.mp hzd.2
      exact (hre.eventually (gt_mem_nhds hzb)).mono
        (fun n hn => ⟨(hu n).1, WithTop.coe_lt_coe.mpr hn⟩)
  have hlim := (hg z.re hzd).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hre, hev⟩)
  exact le_of_tendsto_of_tendsto him hlim (hev.mono (fun n hn => (hu n).2 hn))

/-- Helper toward Lemma 5.5: a proper graph ray rooted on the ambient
boundary separates points below it from the component based west of its root. -/
private theorem gluing_graphRay_below_not_mem_component
    {S : Set ℂ} {x₀ a : ℝ} {X : WithTop ℝ} {g f : ℝ → ℝ}
    (hgraph : S = {q | q.re ∈ rayDomain x₀ X ∧ q.im = g q.re})
    (hg : ContinuousOn g (rayDomain x₀ X))
    (hesc : ∀ M : ℝ, ∃ b ∈ rayDomain x₀ X,
      ∀ t ∈ rayDomain x₀ X, b ≤ t → M ≤ g t)
    (hroot : (⟨x₀, f x₀⟩ : ℂ) ∈ S) (ha : a < x₀)
    {y z : ℂ} (hy : y ∈ S) (hre : y.re = z.re) (him : z.im < y.im) :
    z ∉ connectedComponentIn ({q : ℂ | f q.re ≤ q.im} \ S)
      (⟨a, f a⟩ : ℂ) := by
  let U : Set ℂ := {q | q.re ≤ x₀} ∪
    {q | q.re ∈ rayDomain x₀ X ∧ g q.re ≤ q.im}
  let D : Set ℂ := {q | x₀ ≤ q.re ∧
    (q.re ∈ rayDomain x₀ X → q.im ≤ g q.re)}
  have hU : IsClosed U :=
    (isClosed_Iic.preimage Complex.continuous_re).union
      (gluing_graphRay_epigraph_closed hg hesc)
  have hD : IsClosed D := gluing_graphRay_hypograph_closed hg
  have hcover : (Set.univ : Set ℂ) ⊆ U ∪ D := by
    intro q _
    by_cases hq : q.re ≤ x₀
    · exact Or.inl (Or.inl hq)
    · by_cases hd : q.re ∈ rayDomain x₀ X
      · by_cases hh : g q.re ≤ q.im
        · exact Or.inl (Or.inr ⟨hd, hh⟩)
        · exact Or.inr ⟨(lt_of_not_ge hq).le, fun _ => (lt_of_not_ge hh).le⟩
      · exact Or.inr ⟨(lt_of_not_ge hq).le, fun hh => (hd hh).elim⟩
  have hr := hroot
  rw [hgraph] at hr hy
  simp only [Set.mem_ofPred_eq] at hr hy
  rw [hre] at hy
  have hbase : (⟨a, f a⟩ : ℂ) ∈ {q : ℂ | f q.re ≤ q.im} \ S := by
    refine ⟨show f a ≤ f a from le_rfl, ?_⟩
    intro hh
    rw [hgraph] at hh
    exact (not_le_of_gt ha) hh.1.1
  intro hz
  obtain ⟨q, hqC, hqU, hqD⟩ := isPreconnected_closed_iff.mp
    isPreconnected_connectedComponentIn U D hU hD
    (fun q _ => hcover (Set.mem_univ q))
    ⟨⟨a, f a⟩, mem_connectedComponentIn hbase, Or.inl ha.le⟩
    ⟨z, hz, hy.1.1, fun _ => him.le.trans hy.2.le⟩
  have hq := connectedComponentIn_subset _ _ hqC
  apply hq.2
  rw [hgraph]
  rcases hqU with hqw | hqu
  · have heq : q.re = x₀ := le_antisymm hqw hqD.1
    have hdom : q.re ∈ rayDomain x₀ X := heq ▸ hr.1
    refine ⟨hdom, le_antisymm (hqD.2 hdom) ?_⟩
    have hf : f q.re ≤ q.im := hq.1
    rw [heq] at hf ⊢
    rw [← hr.2]
    exact hf
  · exact ⟨hqu.1, le_antisymm (hqD.2 hqu.1) hqu.2⟩




theorem boundaryGluing_below_trace_not_mem_leftOpen {y z : ℂ}
    (hy : y ∈ m0GeodesicTrace hp P) (hre : y.re = z.re) (him : z.im < y.im) :
    z ∉ m0GeodesicLeftOpen hp P := by
  let f := seamFun (shiftedStream W 0) h (H.1 0)
  let a := seamX (shiftedStream W 0) h (H.1 0) (k - 1)
  have hpos (j : ℤ) : (WholePlanePastGlueDrawing.glueDrawing W h hp H).pos
      ((m0CutData W H h hLL).x j) =
        (⟨seamX (shiftedStream W 0) h (H.1 0) j,
          f (seamX (shiftedStream W 0) h (H.1 0) j)⟩ : ℂ) := by
    rw [(m0CutData W H h hLL).x_eq h hLL j, m0Geodesic_pos_runZero hp]
    exact boundaryVertex_pos_eq (shiftedStream W 0) h (H.1 0) j
  obtain ⟨X, g, _, hg, hgraph, hesc⟩ := m0GeodesicTrace_properGraphRay hp P
  have hroot := m0Geodesic_root_pos_mem_trace hp P
  rw [hpos k] at hroot
  unfold m0GeodesicLeftOpen
  rw [hpos (k - 1)]
  exact gluing_graphRay_below_not_mem_component hgraph hg hesc hroot
    (seamX_strictMono (shiftedStream W 0) h (H.1 0) (show k - 1 < k by omega))
    hy hre him



theorem boundaryGluing_below_trace_mem_rightRegion {y z : ℂ}
    (hy : y ∈ m0GeodesicTrace hp P) (hre : y.re = z.re) (him : z.im < y.im)
    (hz : z ∈ m0GeodesicAmbientRegion W H h) :
    z ∈ m0GeodesicSideRegion hp P .right :=
  ⟨hz, boundaryGluing_below_trace_not_mem_leftOpen W h k longest hp P hy hre him⟩




theorem boundaryGluing_seam_departure_right_of_arg_lt (e i : ℕ)
    (he : e ∉ m0GeodesicEdges P)
    (hi : edgeWest (shiftedStream W 0) e =
      edgeWest (shiftedStream W 0) (P.codePath.edge i))
    (ha : Complex.arg ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (e, false))).initialDirection <
      Complex.arg ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (m0GeodesicSeam P i))).initialDirection) :
    e ∈ (m0GeodesicSide hp P .right).edges := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let A := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hs : (G.arc (wholePlaneDartι W 0 (e, false))).start =
      (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i))).start := by
    dsimp only [G]
    rw [WholePlanePastGlueM0Restriction.restrict_arc W h hp H (e, false),
      WholePlanePastGlueM0Restriction.restrict_arc W h hp H (m0GeodesicSeam P i),
      A.arc_start, A.arc_start]
    exact congrArg A.pos hi
  obtain ⟨z, hz, y, hy, hre, him⟩ := gluing_initial_order_points
    (G.arc (wholePlaneDartι W 0 (e, false)))
    (G.arc (wholePlaneDartι W 0 (m0GeodesicSeam P i)))
    (gluing_runZero_arc_graph W h hp e).2
    (gluing_runZero_arc_graph W h hp (P.codePath.edge i)).2
    (G.arc_length _) (G.arc_length _) hs ha
  have hyP := m0Geodesic_arc_subset_trace hp P i hy.1
  have hzR := boundaryGluing_below_trace_not_mem_leftOpen W h k longest hp P
    hyP hre.symm him
  have hzP : z ∉ m0GeodesicTrace hp P := by
    obtain ⟨X, g, _, _, hgraph, _⟩ := m0GeodesicTrace_properGraphRay hp P
    intro hzP
    rw [hgraph] at hyP hzP
    have heq : z.im = y.im := hzP.2.trans ((congrArg g hre).trans hyP.2.symm)
    exact (ne_of_lt him) heq
  exact (boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P
    he hz hzP).2.mpr hzR



theorem boundaryGluing_hat_right_seam_departure
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (e i : ℕ)
    (he : EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e)
    (hi : edgeWest (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e =
      ((sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime
        ⟨boundaryFutureHattedPath k W, hqMode⟩).initial i).1.id)
    (hoff : ∀ j : ℕ, e ≠ (sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩).edge j)
    (hs : boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingRightHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode) :
    boundaryGluingHatEdgeMap W h k hτ e ∈ (m0GeodesicSide hp P .right).edges := by
  let q : selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime := ⟨boundaryFutureHattedPath k W, hqMode⟩
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime q
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let φ := boundaryGluingHatEdgeMap W h k hτ
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  have heoff : φ e ∉ m0GeodesicEdges P := by
    rintro ⟨j, hj⟩
    exact hoff j (boundaryGluingHatEdgeMap_injective W h k hτ
      (hj.symm.trans (hid j)))
  have hc := boundaryGluing_decoded_stream W h k hτ
  have heq : edgeWest (hatCodes u hτ) e = edgeWest (hatCodes u hτ) (Q.edge i) := by
    rw [← hc]
    exact hi.trans (Q.edge_outgoing_at_initial _ i).2.symm
  have hφ (a : ℕ) : φ a = kmswShiftEdgeMapAll w t
      (hatLimitEdgeMap u hτ a) (hatLimitEdgeMap u hτ a) :=
    boundaryGluingEdgeMap_eq_shift W h k _
  have hew := (shiftHat_edge_incidence w t hτ e).1
  have hpw := (shiftHat_edge_incidence w t hτ (Q.edge i)).1
  dsimp only at hew hpw
  erw [← hφ e] at hew
  erw [← hφ (Q.edge i)] at hpw
  have hwest : edgeWest w (φ e) = edgeWest w (P.codePath.edge i) := by
    rw [hid i]
    exact hew.trans ((congrArg
      (fun a => limitVertexMap (kmswShiftVertexMapAll w t) u (hatLimitVertexMap u hτ a))
      heq).trans hpw.symm)
  have harg := (boundaryGluing_hatSideEdges_iff_glued_launch_arg W h k hτ
    (if longest then XDP.ldp else XDP.sdp) hqMode H hp hfin .right e i he hi hoff).mp hs
  apply boundaryGluing_seam_departure_right_of_arg_lt W h k longest hp P
    (φ e) i heoff hwest
  change _ < Complex.arg ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
      (wholePlaneDartι W 0 (P.codePath.edge i, false))).initialDirection
  rw [hid i]
  exact harg




theorem boundaryGluing_hat_right_of_west_mem_right
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (e : ℕ)
    (he : EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e)
    (hs : boundaryGluingHatEdgeMap W h k hτ e ∈ boundaryGluingRightHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode)
    (hw : edgeWest (shiftedStream W 0) (boundaryGluingHatEdgeMap W h k hτ e) ∈
      (m0GeodesicSide hp P .right).vertices) :
    boundaryGluingHatEdgeMap W h k hτ e ∈ (m0GeodesicSide hp P .right).edges := by
  let φ := boundaryGluingHatEdgeMap W h k hτ
  let ψ := boundaryGluingHatVertexMap W h k hτ
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  by_cases hoff : φ e ∈ m0GeodesicEdges P
  · exact (m0GeodesicEdges_subset_both hp P hoff).2
  · have heoff (i : ℕ) : e ≠ Q.edge i := by
      intro hi
      exact hoff ⟨i, (hid i).trans (congrArg φ hi.symm)⟩
    let p := G.pos (wholePlaneVertexι W 0 (edgeWest (shiftedStream W 0) (φ e)))
    have hpstart : p ∈ (G.arc (wholePlaneDartι W 0 (φ e, false))).image := by
      exact Or.inl (G.arc_start (wholePlaneDartι W 0 (φ e, false))).symm
    by_cases hpP : p ∈ m0GeodesicTrace hp P
    · have hew : edgeWest (shiftedStream W 0) (φ e) = ψ (edgeWest z e) := by
        have hh := (boundaryGluing_hat_edge_endpoints W h k hτ e).1
        rw [← boundaryGluing_decoded_stream W h k hτ] at hh
        exact hh
      have hpP' : G.pos (wholePlaneVertexι W 0 (ψ (edgeWest z e))) ∈
          m0GeodesicTrace hp P := hew ▸ hpP
      obtain ⟨i, hi⟩ := (boundaryGluing_hatVertex_mem_trace_iff W h k hτ
        longest hp P hqMode Tpath hfin hleft (edgeWest z e)).mp hpP'
      exact boundaryGluing_hat_right_seam_departure W h k hτ longest hp P
        hqMode Tpath hfin hleft e i he hi.symm heoff hs
    · have hw' : p ∈ m0GeodesicSideRegion hp P .right := hw
      have hpR : p ∉ m0GeodesicLeftOpen hp P := hw'.2
      exact (boundaryGluing_sideEdges_iff_off_trace_point W h k longest hp P
        hoff hpstart hpP).2.mpr hpR



theorem boundaryGluing_finiteCut_right_edges
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (t : ℕ) {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B (if longest then XDP.ldp else XDP.sdp) = m)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) t))
    (hprefix : ((selectedGeodesicOfLen R.B
      (if longest then XDP.ldp else XDP.sdp) hR).darts.map I.toEquiv).map
        (fun d => d.1.val) = List.ofFn (fun j : Fin m =>
          (sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime
            ⟨boundaryFutureHattedPath k W, hqMode⟩).edge j.val))
    (d : Fin (ancestorPosHalfRep R hR .right).dartCount) :
    boundaryGluingHatEdgeMap W h k hτ
      (ancestorPosDartId _ t R hR I .right d).1 ∈ (m0GeodesicSide hp P .right).edges := by
  classical
  let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  let Q := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  let B := (ancestorPosHalfRep R hR .right).B
  let f := ancestorPosDartId z t R hR I .right
  let F := ancestorPosVertexId z t R hR I .right
  let φ := boundaryGluingHatEdgeMap W h k hτ
  let ψ := boundaryGluingHatVertexMap W h k hτ
  have hside (c : Fin (ancestorPosHalfRep R hR .right).dartCount) :
      φ (f c).1 ∈ boundaryGluingRightHatEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode := by
    apply (boundaryGluing_hatSideEdges_iff_finiteCut W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode t R hR I hprefix
      .right (ancestorPosDartMap R hR .right c)).mpr
    have hh : ancestorPosDartMap R hR .right c ∈
        Set.range (ancestorPosDartMap R hR .right) := ⟨c, rfl⟩
    rw [ancestorPosDartMap_range] at hh
    exact hh
  have hend (c : Fin (ancestorPosHalfRep R hR .right).dartCount) (ht : B.map.tail c) :
      edgeWest (shiftedStream W 0) (φ (f c).1) = ψ (F (dartTailVertex B.map c)) ∧
      edgeEast (shiftedStream W 0) (φ (f c).1) = ψ (F (dartHeadVertex B.map c)) := by
    have ho := (ancestorPos_ids_oriented z t R hR I .right c).mp ht
    have he := ancestorPos_ids_endpoints z t R hR I .right c
    rw [ho.2] at he
    have hg := boundaryGluing_hat_edge_endpoints W h k hτ (f c).1
    rw [← boundaryGluing_decoded_stream W h k hτ] at hg
    exact ⟨hg.1.trans (congrArg ψ he.1.symm),
      hg.2.trans (congrArg ψ he.2.symm)⟩
  have hforward (c : Fin (ancestorPosHalfRep R hR .right).dartCount)
      (ht : B.map.tail c)
      (hv : ψ (F (dartTailVertex B.map c)) ∈ (m0GeodesicSide hp P .right).vertices) :
      φ (f c).1 ∈ (m0GeodesicSide hp P .right).edges := by
    apply boundaryGluing_hat_right_of_west_mem_right W h k hτ longest hp P
      hqMode Tpath hfin hleft (f c).1
      ((ancestorPos_ids_oriented z t R hR I .right c).mp ht).1 (hside c)
    rw [(hend c ht).1]
    exact hv
  have hroot : ψ (F B.source) ∈ (m0GeodesicSide hp P .right).vertices := by
    have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
      hp Tpath P hfin hleft
    have he := (boundaryGluing_hat_edge_endpoints W h k hτ (Q.edge 0)).1
    have hq : edgeWest (hatCodes (boundaryGluingFutureStream W h k) hτ) (Q.edge 0) = 0 :=
      (congrArg (fun w => edgeWest w (Q.edge 0))
        (boundaryGluing_decoded_stream W h k hτ)).symm.trans Q.first_edge_outgoing.2
    rw [hq, ← hid 0] at he
    have hsource : F B.source = 0 :=
      ancestorPos_source_id_of_prefix z Q t R hR I hprefix .right
    have he' : edgeWest (shiftedStream W 0) (P.codePath.edge 0) = ψ 0 := he
    rw [hsource, ← he']
    exact (m0GeodesicSide_endpoints hp P .right _
      (m0GeodesicEdges_subset_both hp P (m0GeodesicSeam_mem_edges P 0)).2).1
  have hvertex (v : MapVertex B.map) : ψ (F v) ∈ (m0GeodesicSide hp P .right).vertices := by
    obtain ⟨j, A, _⟩ := exists_simple_source_pathBase B v
    have hreach : Relation.ReflTransGen B.map.directedStep B.source v := by
      have hr (i : ℕ) (hi : i ≤ j) : Relation.ReflTransGen B.map.directedStep
          (A.vertices.get ⟨0, by rw [A.vertices_length]; omega⟩)
          (A.vertices.get ⟨i, by rw [A.vertices_length]; omega⟩) := by
        induction i with
        | zero => exact .refl
        | succ i ih =>
          have hs := A.edge_step ⟨i, by rw [A.darts_length]; omega⟩
          exact (ih (by omega)).tail ⟨_, hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩
      simpa only [A.start_vertex, A.end_vertex] using hr j le_rfl
    clear A
    induction hreach with
    | refl => exact hroot
    | @tail b c _ hbc ih =>
      obtain ⟨a, _, ht, hb, hc⟩ := hbc
      change dartTailVertex B.map a = b at hb
      change dartHeadVertex B.map a = c at hc
      have ha := hforward a ht (by rw [hb]; exact ih)
      have hh := (m0GeodesicSide_endpoints hp P .right _ ha).2
      change edgeEast (shiftedStream W 0) (φ (f a).1) ∈ _ at hh
      rw [(hend a ht).2, hc] at hh
      exact hh
  by_cases ht : B.map.tail d
  · exact hforward d ht (hvertex _)
  · have ht' : B.map.tail (B.map.edgeInv d) := by
      by_contra hn
      exact ht ((B.map.tail_iff d (B.noMissingDarts d)).mpr hn)
    have hh := hforward (B.map.edgeInv d) ht' (hvertex _)
    have he := congrArg Prod.fst (ancestorPos_ids_opposite z t R hR I .right d)
    exact he ▸ hh




theorem boundaryGluingRightHatEdges_subset_right
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath) :
    boundaryGluingRightHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode ⊆
        (m0GeodesicSide hp P .right).edges := by
  rintro e ⟨a, ha, rfl⟩
  have hs : boundaryGluingHatEdgeMap W h k hτ a ∈ boundaryGluingHatSideEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode .right := ⟨a, ha, rfl⟩
  obtain ⟨t, ℓ, r, n, m, R, hR, I, hprefix, d, hd, hleftHalf⟩ :=
    (boundaryGluing_hatSideEdges_iff_exists_finiteCut W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode .right a).mp hs
  have hrange : d ∈ Set.range (ancestorPosDartMap R hR .right) := by
    rw [ancestorPosDartMap_range]
    exact hleftHalf
  obtain ⟨c, rfl⟩ := hrange
  have hh := boundaryGluing_finiteCut_right_edges W h k hτ longest hp P
    hqMode Tpath hfin hleft t R hR I hprefix c
  change boundaryGluingHatEdgeMap W h k hτ (I.toEquiv
    (ancestorPosDartMap R hR .right c)).1.val ∈ _ at hh
  rw [hd] at hh
  exact hh



theorem boundaryGluingRightHatEdges_sdiff_seam_subset_right
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath) :
    boundaryGluingRightHatEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode \
      boundaryGluingHatSeamEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode ⊆
          (m0GeodesicSide hp P .right).edges :=
  Set.sdiff_subset.trans (boundaryGluingRightHatEdges_subset_right W h k hτ
    longest hp P hqMode Tpath hfin hleft)

/-- Helper toward Lemma 5.5: a continuous upper boundary separates its
closed finite region from a component based strictly west of the region.
The lower boundary is the ambient boundary, including missing geometry. -/
private theorem gluing_finite_upper_barrier
    {C : Set ℂ} {a b : ℝ} {f g : ℝ → ℝ} {p : ℂ}
    (hC : IsPreconnected C) (hpC : p ∈ C) (hpa : p.re < a)
    (hambient : C ⊆ {q : ℂ | f q.re ≤ q.im})
    (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b))
    (ha : f a = g a) (hb : f b = g b)
    (havoid : Disjoint C (graphOver a b g)) :
    Disjoint C (closedGraphRegion a b f g) := by
  let U : Set ℂ := {q | q.re ≤ a} ∪ {q | b ≤ q.re} ∪
    {q | q.re ∈ Set.Icc a b ∧ g q.re ≤ q.im}
  let D := closedGraphRegion a b f g
  have hE : IsClosed {q : ℂ | q.re ∈ Set.Icc a b ∧ g q.re ≤ q.im} := by
    apply IsSeqClosed.isClosed
    intro u z hu hz
    have hre := Complex.continuous_re.tendsto z |>.comp hz
    have him := Complex.continuous_im.tendsto z |>.comp hz
    have hzd : z.re ∈ Set.Icc a b :=
      ⟨ge_of_tendsto' hre (fun n => (hu n).1.1),
        le_of_tendsto' hre (fun n => (hu n).1.2)⟩
    refine ⟨hzd, ?_⟩
    have hlim := (hg z.re hzd).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨hre, Filter.Eventually.of_forall (fun n => (hu n).1)⟩)
    exact le_of_tendsto_of_tendsto' hlim him (fun n => (hu n).2)
  have hU : IsClosed U :=
    ((isClosed_Iic.preimage Complex.continuous_re).union
      (isClosed_Ici.preimage Complex.continuous_re)).union hE
  have hD : IsClosed D := isClosed_closedGraphRegion hf hg
  apply Set.disjoint_left.mpr
  intro z hzC hzD
  obtain ⟨q, hqC, hqU, hqD⟩ := isPreconnected_closed_iff.mp hC U D hU hD
    (by
      intro q hqC
      by_cases hqa : q.re ≤ a
      · exact Or.inl (Or.inl (Or.inl hqa))
      by_cases hqb : b ≤ q.re
      · exact Or.inl (Or.inl (Or.inr hqb))
      by_cases hqg : g q.re ≤ q.im
      · exact Or.inl (Or.inr ⟨⟨(lt_of_not_ge hqa).le,
          (lt_of_not_ge hqb).le⟩, hqg⟩)
      · exact Or.inr ⟨(lt_of_not_ge hqa).le, (lt_of_not_ge hqb).le,
          hambient hqC, (lt_of_not_ge hqg).le⟩)
    ⟨p, hpC, Or.inl (Or.inl hpa.le)⟩ ⟨z, hzC, hzD⟩
  apply Set.disjoint_left.mp havoid hqC
  refine ⟨hqD.1, hqD.2.1, le_antisymm hqD.2.2.2 ?_⟩
  rcases hqU with (hqa | hqb) | hqg
  · have heq : q.re = a := le_antisymm hqa hqD.1
    have hh := hambient hqC
    change f q.re ≤ q.im at hh
    rw [heq, ha] at hh
    simpa only [heq] using hh
  · have heq : q.re = b := le_antisymm hqD.2.1 hqb
    have hh := hambient hqC
    change f q.re ≤ q.im at hh
    rw [heq, hb] at hh
    simpa only [heq] using hh
  · exact hqg.2

/-- Helper toward Lemma 5.5: the finite stage's lower and upper graphs
join at both endpoints, with geometric boundary edges retained. -/
private theorem gluing_stage_boundary_joins (w : ℕ → Fin 3) (n : ℕ)
    {A : StageDrawing w n} (G : MonotoneStageInvariant w n A) :
    G.lower G.xmin = G.upper G.xmin ∧ G.lower G.xmax = G.upper G.xmax := by
  let U := (kmswStage w n).UL ++ (kmswStage w n).UR
  let L := (kmswStage w n).LL ++ (kmswStage w n).LR
  have hUn : U ≠ [] := (kmswStage_boundary_nonempty w n).1
  have hLn : L ≠ [] := (kmswStage_boundary_nonempty w n).2
  have hbound (e : ℕ) (he : e ∈ U ∨ e ∈ L) : e < (kmswStage w n).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    simp only [U, L, List.mem_append] at he ⊢
    tauto
  have hstart (e : ℕ) (he : e ∈ U ∨ e ∈ L) :
      layoutPos w n ((kmswStage w n).west e) ∈ (layoutArc w n e).image := by
    rw [← layoutArc_start w n e (hbound e he)]
    exact Or.inl rfl
  have hfinish (e : ℕ) (he : e ∈ U ∨ e ∈ L) :
      layoutPos w n ((kmswStage w n).east e) ∈ (layoutArc w n e).image := by
    rw [← layoutArc_finish w n e (hbound e he)]
    exact gluing_finish_mem_image _
  have hs := (kmswStage_boundary_endpoints w n).1
  have ht := (kmswStage_boundary_endpoints w n).2
  change (kmswStage w n).west (U.head hUn) =
    (kmswStage w n).west (L.head hLn) at hs
  change (kmswStage w n).east (U.getLast hUn) =
    (kmswStage w n).east (L.getLast hLn) at ht
  constructor
  · rw [G.xmin_eq_upper_start]
    have hu := G.upper_eq_arc_height (List.head_mem hUn)
      (hstart (U.head hUn) (Or.inl (List.head_mem hUn)))
    have hl := G.lower_eq_arc_height (List.head_mem hLn)
      (hstart (L.head hLn) (Or.inr (List.head_mem hLn)))
    rw [← hs] at hl
    exact hl.trans hu.symm
  · rw [G.xmax_eq_upper_end]
    have hu := G.upper_eq_arc_height (List.getLast_mem hUn)
      (hfinish (U.getLast hUn) (Or.inl (List.getLast_mem hUn)))
    have hl := G.lower_eq_arc_height (List.getLast_mem hLn)
      (hfinish (L.getLast hLn) (Or.inr (List.getLast_mem hLn)))
    rw [← ht] at hl
    exact hl.trans hu.symm





theorem boundaryGluingPrefixEdges_subset_right
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    boundaryGluingPrefixEdges W h k ⊆ (m0GeodesicSide hp P .right).edges := by
  classical
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let A := familyQ w (monotone_family_all w) t
  let G := familyG w (monotone_family_all w) t
  let B := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let f := seamFun w h (H.1 0)
  have hUL : (kmswStage w t).UL = [act w t] := by
    by_cases hk0 : k = 0
    · subst k
      rw [show t = 0 from boundaryHitTime_zero w h]
      rfl
    · exact (leftHit_UL_singleton_and_west_endpoint w h (by omega)).1
  have harc (e : ℕ) (he : e < (kmswStage w t).nextEdge) :
      B.arc (wholePlaneDartι W 0 (e, false)) =
        A.arc (⟨e, he⟩, false) := by
    exact (WholePlanePastGlueM0Restriction.restrict_arc W h hp H (e, false)).trans
      (familyDrawing_arc w (H.1 0) (monotone_family_all w) t (⟨e, he⟩, false))
  have hseam (x : ℝ) (hx : x ∈ Set.Icc G.xmin G.xmax) : f x = G.lower x :=
    seamFun_eq_lower w h (H.1 0) t x hx
  have hxmin : G.xmin = seamX w h (H.1 0) k := by
    rw [G.xmin_eq_active_west_of_UL_dropLast_reverse_nil
      (by rw [hUL]; rfl)]
    change (layoutPos w t ((kmswStage w t).west (act w t))).re = _
    have he := (edge_endpoints_eq w (act_lt_nextEdge w (m := t) le_rfl)).1
    rw [he, ← boundaryVertex_eq_edgeWest_hit w h k]
    have hv := (kmswStage_endpoints_lt_nextVertex w t (act w t)
      (act_lt_nextEdge w le_rfl)).1
    rw [he, ← boundaryVertex_eq_edgeWest_hit w h k] at hv
    rw [← monotoneLimitDrawing_pos_layout w (H.1 0) _ t _ hv]
    rfl
  have hupper : Disjoint (m0GeodesicLeftOpen hp P)
      (graphOver G.xmin G.xmax G.upper) := by
    apply Set.disjoint_left.mpr
    intro q hqL hqU
    rw [G.upper_trace] at hqU
    obtain ⟨e, hqe⟩ := Set.mem_iUnion.mp hqU
    obtain ⟨he, hqe⟩ := Set.mem_iUnion.mp hqe
    have heb : e < (kmswStage w t).nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge w t).2 e (by
        simp only [List.mem_append] at he ⊢
        tauto)
    have heR : e ∈ boundaryGluingUpperRightEdges W h k := by
      rw [hUL] at he
      rcases List.mem_append.mp he with he | he
      · exact Or.inl (List.mem_singleton.mp he)
      · exact Or.inr he
    have heHR := boundaryGluingUpperRightEdges_subset_rightHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode hfin heR
    have heSR := boundaryGluingRightHatEdges_subset_right W h k hτ longest hp P
      hqMode Tpath hfin hleft heHR
    have hqe' : q ∈ (B.arc (wholePlaneDartι W 0 (e, false))).image := by
      rw [harc e heb]
      simpa only [stageEdgeTrace, dite_eq_left heb] using hqe
    exact (heSR hqe').2 hqL
  let p := B.pos ((m0CutData W H h hLL).x (k - 1))
  have hpC : p ∈ m0GeodesicLeftOpen hp P := m0Geodesic_previous_pos_mem_leftOpen hp P
  have hpa : p.re < G.xmin := by
    rw [hxmin]
    dsimp only [p, B]
    rw [(m0CutData W H h hLL).x_eq h hLL (k - 1), m0Geodesic_pos_runZero hp]
    exact seamX_strictMono w h (H.1 0) (by omega)
  have hjoins := gluing_stage_boundary_joins w t G
  have hbarrier : Disjoint (m0GeodesicLeftOpen hp P)
      (closedGraphRegion G.xmin G.xmax f G.upper) :=
    gluing_finite_upper_barrier isPreconnected_connectedComponentIn hpC hpa
      (fun q hq => (m0GeodesicLeftOpen_subset hp P hq).1)
      (seamFun_continuous w h (H.1 0)).continuousOn G.upper_continuous
      ((hseam _ ⟨le_rfl, G.hx⟩).trans hjoins.1)
      ((hseam _ ⟨G.hx, le_rfl⟩).trans hjoins.2) hupper
  intro e he q hq
  have heb : e < (kmswStage w t).nextEdge := he
  have hqA : q ∈ A.image := by
    apply Or.inr
    refine ⟨(⟨e, heb⟩, false), ?_⟩
    rw [← harc e heb]
    exact hq
  have hb := G.image_bounds hqA
  have hqD : q ∈ closedGraphRegion G.xmin G.xmax f G.upper :=
    ⟨hb.1, hb.2.1, (hseam _ ⟨hb.1, hb.2.1⟩).symm ▸ hb.2.2.1, hb.2.2.2⟩
  exact ⟨m0Geodesic_arc_subset_ambient hp e hq,
    fun hqL => Set.disjoint_left.mp hbarrier hqL hqD⟩



theorem boundaryGluingPrefixEdges_sdiff_seam_subset_right
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    boundaryGluingPrefixEdges W h k \
      boundaryGluingHatSeamEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode ⊆
          (m0GeodesicSide hp P .right).edges :=
  Set.sdiff_subset.trans (boundaryGluingPrefixEdges_subset_right W h k longest hp P
    hτ hqMode Tpath hfin hleft hk)

/-- Helper toward Lemma 5.5: two covering partitions with the same common
seam agree once both block inclusions have been proved. -/
private theorem gluing_eq_of_partition_inclusions {α : Type*}
    {A B L R S : Set α} (hcover : A ∪ B = Set.univ)
    (hAB : A ∩ B = S) (hLR : L ∩ R = S)
    (hAL : A ⊆ L) (hBR : B ⊆ R) : L = A ∧ R = B := by
  constructor
  · apply Set.Subset.antisymm ?_ hAL
    intro e heL
    have hecov := Set.eq_univ_iff_forall.mp hcover e
    rcases hecov with heA | heB
    · exact heA
    · have heS : e ∈ S := hLR ▸ ⟨heL, hBR heB⟩
      exact (show e ∈ A ∩ B from hAB.symm ▸ heS).1
  · apply Set.Subset.antisymm ?_ hBR
    intro e heR
    have hecov := Set.eq_univ_iff_forall.mp hcover e
    rcases hecov with heA | heB
    · have heS : e ∈ S := hLR ▸ ⟨hAL heA, heR⟩
      exact (show e ∈ A ∩ B from hAB.symm ▸ heS).2
    · exact heB



theorem boundaryGluing_nonneg_side_identities
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) :
    (m0GeodesicSide hp P .right).edges = boundaryGluingRightHatEdges W h k hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode ∧
    (m0GeodesicSide hp P .left).edges = boundaryGluingPrefixMinusEdges W h k ∪
      boundaryGluingLeftHatEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode ∪
      boundaryGluingPrimedEdges W h k hτ := by
  have hpart := (boundaryGluing_edge_partitions W h k hτ
    (if longest then XDP.ldp else XDP.sdp) hqMode hfin).1 hk
  have hactual := boundaryGluing_m0SideEdges_inter_eq_hatSeam W h k hτ longest hqMode
    hp Tpath P hfin hleft
  have hAL := Set.union_subset
    (Set.union_subset (boundaryGluingPrefixMinusEdges_subset_left W h k longest hp P hk)
      (boundaryGluingLeftHatEdges_subset_left W h k hτ longest hp P
        hqMode Tpath hfin hleft))
    (boundaryGluingPrimedEdges_subset_left W h k hτ longest hp P
      hqMode Tpath hfin hleft)
  have heq := gluing_eq_of_partition_inclusions hpart.1 hpart.2 hactual hAL
    (boundaryGluingRightHatEdges_subset_right W h k hτ longest hp P
      hqMode Tpath hfin hleft)
  exact ⟨heq.2, heq.1⟩



theorem boundaryGluing_nonpos_side_identities
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    (m0GeodesicSide hp P .left).edges = boundaryGluingPrimedEdges W h k hτ ∪
      boundaryGluingLeftHatEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode ∧
    (m0GeodesicSide hp P .right).edges = boundaryGluingPrefixEdges W h k ∪
      boundaryGluingRightHatEdges W h k hτ
        (if longest then XDP.ldp else XDP.sdp) hqMode := by
  have hpart := (boundaryGluing_edge_partitions W h k hτ
    (if longest then XDP.ldp else XDP.sdp) hqMode hfin).2 hk
  have hactual := boundaryGluing_m0SideEdges_inter_eq_hatSeam W h k hτ longest hqMode
    hp Tpath P hfin hleft
  exact gluing_eq_of_partition_inclusions hpart.1 hpart.2 hactual
    (Set.union_subset (boundaryGluingPrimedEdges_subset_left W h k hτ longest hp P
      hqMode Tpath hfin hleft)
      (boundaryGluingLeftHatEdges_subset_left W h k hτ longest hp P
        hqMode Tpath hfin hleft))
    (Set.union_subset (boundaryGluingPrefixEdges_subset_right W h k longest hp P
      hτ hqMode Tpath hfin hleft hk)
      (boundaryGluingRightHatEdges_subset_right W h k hτ longest hp P
        hqMode Tpath hfin hleft))




theorem boundaryGluingSideIdentities_proved
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath) :
    BoundaryGluingSideIdentities W h k hτ longest hqMode hp P :=
  ⟨boundaryGluing_nonneg_side_identities W h k hτ longest hp P
      hqMode Tpath hfin hleft,
    boundaryGluing_nonpos_side_identities W h k hτ longest hp P
      hqMode Tpath hfin hleft⟩

end GluedSeamSeeds

end DirectedDistances.PaperProofs.Section5


