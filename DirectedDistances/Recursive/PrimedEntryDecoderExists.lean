module

public import DirectedDistances.Recursive.PrimedEntryDistanceCode
public import DirectedDistances.Recursive.LeftLocalityAssembly

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk Quiver MeasureTheory Filter

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The retained geometric root endpoints never change at later stages. -/
theorem primedEntryOuterVertex_root (u : ℕ → Fin 3) (n : ℕ) :
    primedEntryOuterVertex (kmswStage u n) 0 = some 1 ∧
      primedEntryOuterVertex (kmswStage u n) 1 = some 0 := by
  have he := kmswStage_endpoints_stable u (Nat.zero_le n)
    (show 0 < (kmswStage u 0).nextEdge from Nat.zero_lt_one)
  change (kmswStage u n).west 0 = 0 ∧ (kmswStage u n).east 0 = 1 at he
  simp only [primedEntryOuterVertex, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, he.1, he.2, and_self]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The initial left exit is the first negative boundary hit, with no extra witness choice. -/
theorem primedEntry_initialExit_eq_boundaryHit (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) :
    walkNL w h 0 = boundaryHitTime w hb (-1) := by
  classical
  have hz : L w 0 = 0 := rfl
  have hs := walkNL_spec w h 0
  rw [walkNR_zero, hz] at hs
  have ht := boundaryHitTime_left_spec w hb (k := -1) (by omega)
  have hp : 1 ≤ boundaryHitTime w hb (-1) := by
    by_contra hn
    have he : boundaryHitTime w hb (-1) = 0 := by omega
    rw [he, hz] at ht
    contradiction
  have hf : walkNL w h 0 = Nat.find (h.1 0) := rfl
  have hbfind : boundaryHitTime w hb (-1) =
      Nat.find (hb.leftHit (-1) (by omega)) := by
    simp only [boundaryHitTime, dite_eq_right (by omega : (-1 : ℤ) ≠ 0),
      dite_eq_right (by omega : ¬ (0 : ℤ) < -1)]
  apply Nat.le_antisymm
  · rw [hf]
    exact Nat.find_min' (h.1 0) ⟨hp, by rw [hz]; exact ht⟩
  · rw [hbfind]
    exact Nat.find_min' (hb.leftHit (-1) (by omega)) hs.2

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
H' maps the local east root to x₀ and the local west root to x₋₁. -/
theorem primedEntryVertexMap_root (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hb : BoundaryHitWitnesses w) :
    primedLimitVertexMap w h 1 = boundaryVertex w hb 0 ∧
      primedLimitVertexMap w h 0 = boundaryVertex w hb (-1) := by
  have h0 := (primedLimit_maps_eq_of_allocated w h 0).2 0
    (show 0 < 2 from by omega)
  have h1 := (primedLimit_maps_eq_of_allocated w h 0).2 1
    (show 1 < 2 from by omega)
  change primedLimitVertexMap w h 0 =
    (kmswStage w (walkNL w h 0)).west (kmswLLCreatedEdge w (walkNL w h 0)) at h0
  change primedLimitVertexMap w h 1 =
    (kmswStage w (walkNL w h 0)).east (kmswLLCreatedEdge w (walkNL w h 0)) at h1
  rw [primedEntry_initialExit_eq_boundaryHit w h hb] at h0 h1
  have he := boundaryVertex_left_root_missing_edge w hb
  exact ⟨h1.trans (he.2.1.trans (boundaryVertex_zero w hb).symm), h0.trans he.1⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The index-zero endpoint identification holds, despite the C18 missing root. -/
theorem primedEntryOuterVertexIdentification_zero_proved (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) :
    PrimedEntryOuterVertexIdentification w h hb 0 := by
  filter_upwards [] with n
  refine ⟨1, (primedEntryOuterVertex_root _ n).1, ?_⟩
  exact (primedEntryVertexMap_root w h hb).1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The index-one endpoint identification uses the west endpoint of the C18 root. -/
theorem primedEntryOuterVertexIdentification_one_proved (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) :
    PrimedEntryOuterVertexIdentification w h hb 1 := by
  filter_upwards [] with n
  exact ⟨0, (primedEntryOuterVertex_root _ n).2,
    (primedEntryVertexMap_root w h hb).2⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The proposed decoder converts only stabilization failure to bottom. -/
@[expose] noncomputable def primedEntryDecoder (u : ℕ → Fin 3) (j k : ℕ) :
    WithBot ℕ :=
  (primedEntryDistanceCode u j k).getD ⊥

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The proposed decoder is measurable, including the failure branch. -/
theorem measurable_primedEntryDecoder : Measurable primedEntryDecoder := by
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro k
  let : MeasurableSpace (Option (WithBot ℕ)) := ⊤
  exact (measurable_of_countable (fun d : Option (WithBot ℕ) => d.getD ⊥)).comp
    (measurable_primedEntryDistanceCode j k)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Both root boundary indices have their exact ambient eventual distance for every glue index. -/
theorem primedEntryBoundaryStageDistance_root_eventually (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (j k : ℕ) (hj : j ≤ 1) :
    ∀ᶠ n in atTop,
      primedEntryBoundaryStageDistance (primedCode (primedSimInput w) h) n j k =
        leftLengthSup (leftPrimedEntryLengths w ⟨boundaryVertex w hb (-(j : ℤ))⟩
          ⟨kmswBeta0Vertices w hfin hb k⟩) := by
  obtain ⟨a, ha, ham⟩ : ∃ a,
      (∀ n, primedEntryOuterVertex
        (kmswStage (primedCode (primedSimInput w) h) n) j = some a) ∧
      primedLimitVertexMap w h a = boundaryVertex w hb (-(j : ℤ)) := by
    have hc : j = 0 ∨ j = 1 := by omega
    rcases hc with rfl | rfl
    · exact ⟨1, fun n => (primedEntryOuterVertex_root _ n).1,
        (primedEntryVertexMap_root w h hb).1⟩
    · exact ⟨0, fun n => (primedEntryOuterVertex_root _ n).2,
        (primedEntryVertexMap_root w h hb).2⟩
  let b := edgeEast (primedCode (primedSimInput w) h)
    (primedBeta0EdgeIndex w h hfin hb hfin k)
  have hglue := primedEntryGlueVertex_eventually w h hfin hb k
  have hdist := primedEntryStageDistance_identification w h hfin a b
  have hbm := primedEntryGlueVertexIdentification_proved w h hfin hb k
  change primedLimitVertexMap w h b = kmswBeta0Vertices w hfin hb k at hbm
  filter_upwards [hglue, hdist] with n hn hd
  unfold primedEntryBoundaryStageDistance
  rw [ha n, hn]
  change primedEntryStageDistance _ n a b = _
  rw [hd, ham, hbm]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The code identifies all first-entry lengths from indices zero and one, including bottom. -/
theorem primedEntryDistanceCode_root_identification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (j k : ℕ) (hj : j ≤ 1) :
    primedEntryDistanceCode (primedCode (primedSimInput w) h) j k =
      some (leftLengthSup (leftPrimedEntryLengths w
        ⟨boundaryVertex w hb (-(j : ℤ))⟩ ⟨kmswBeta0Vertices w hfin hb k⟩)) :=
  (primedEntryDistanceCode_eq_some_iff _ j k _).mpr
    (primedEntryBoundaryStageDistance_root_eventually w h hfin hb j k hj)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The root code identification is simultaneous in all finite-incidence and boundary witnesses. -/
theorem primedEntryDistanceCode_root_identification_ae :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
        (j k : ℕ), j ≤ 1 →
        primedEntryDistanceCode (hatLawPrimedCodes ω) j k =
          some (leftLengthSup (leftPrimedEntryLengths w
            ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩
            ⟨kmswBeta0Vertices w hfin hb k⟩)) := by
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits] with ω h
  dsimp only
  intro hfin hb j k hj
  rw [hatLawPrimedCodes, dite_eq_left h, rightHat_boundaryIdTotal_eq ω hb]
  exact primedEntryDistanceCode_root_identification _ h hfin hb j k hj

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The measurable proposed decoder has the exact simultaneous root-index specification. -/
theorem primedEntryDecoder_root_identification_ae :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
        (j k : ℕ), j ≤ 1 →
        primedEntryDecoder (hatLawPrimedCodes ω) j k =
          leftLengthSup (leftPrimedEntryLengths w
            ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩
            ⟨kmswBeta0Vertices w hfin hb k⟩) := by
  filter_upwards [primedEntryDistanceCode_root_identification_ae] with ω h
  dsimp only
  intro hfin hb j k hj
  unfold primedEntryDecoder
  rw [h hfin hb j k hj, Option.getD_some]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Proved downstream in Recursive/HLRLdpFinal.lean
(primedEntryOuterLLVertexIdentification_proved / primedEntryDecoderExists_proved);
this file proves the cases j ≤ 1. -/
@[expose] def PrimedEntryOuterLLVertexIdentification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) (i : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ a,
    ((kmswStage (primedCode (primedSimInput w) h) n).LL.reverse.map
      (kmswStage (primedCode (primedSimInput w) h) n).west)[i]? = some a ∧
      primedLimitVertexMap w h a = boundaryVertex w hb (-((i + 2 : ℕ) : ℤ))

end DirectedDistances.Recursive
