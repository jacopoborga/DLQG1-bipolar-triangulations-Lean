module

public import DirectedDistances.Recursive.PrimedEntryDistanceCodeSdp
public import DirectedDistances.Recursive.BusemannLeftAlongGeodesicSdp
public import DirectedDistances.Recursive.HLRLdpFinal

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "ThinCode" => (ℕ → Option FiniteThinMap)
local notation "D" =>
  selectedCutCoherentDomain XDP.sdp renewalTime renewalTime_positiveSuccessTime
local notation "Tsdp" =>
  thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The primed SDP decoder uses the same simultaneous witnesses as the LDP decoder. -/
@[expose] def PrimedEntrySdpDecoderExists : Prop :=
  ∃ A : (ℕ → Fin 3) → ℕ → ℕ → ℕ∞, Measurable A ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w), ∀ j k,
        A (hatLawPrimedCodes ω) j k = leftLengthMin
          (leftPrimedEntryLengths w ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩
            ⟨kmswBeta0Vertices w hfin hb k⟩)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Recover a stable local boundary vertex ID, with zero only for failed stabilization. -/
@[expose] noncomputable def primedEntrySdpLocalVertex
    (endpoint : State → ℕ → Option ℕ) (u : ℕ → Fin 3) (j : ℕ) : ℕ :=
  (eventualIntValue 0 (fun n =>
    ((endpoint (kmswStage u n) j).getD 0 : ℤ))).toNat

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Stable endpoint extraction is measurable because every stage uses a finite prefix. -/
private theorem measurable_sdpLocalVertex (endpoint : State → ℕ → Option ℕ) (j : ℕ) :
    Measurable (fun u => primedEntrySdpLocalVertex endpoint u j) := by
  apply (measurable_of_countable Int.toNat).comp
  apply measurable_eventualIntValue 0
  intro n
  refine measurable_of_factors_prefix n _ (fun u v h => ?_)
  rw [kmswStage_congr h]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An eventually constant endpoint is recovered with its exact local ID. -/
private theorem sdpLocalVertex_eq (endpoint : State → ℕ → Option ℕ)
    (u : ℕ → Fin 3) (j a : ℕ)
    (ha : ∀ᶠ n in atTop, endpoint (kmswStage u n) j = some a) :
    primedEntrySdpLocalVertex endpoint u j = a := by
  have hh : ∀ᶠ n in atTop,
      ((endpoint (kmswStage u n) j).getD 0 : ℤ) = (a : ℤ) := by
    filter_upwards [ha] with n hn
    rw [hn, Option.getD_some]
  rw [primedEntrySdpLocalVertex, eventualIntValue_eq 0 hh, Int.toNat_natCast]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Decode the primed SDP at the stable outer and glue boundary vertices.
Unreachable pairs keep the top value of the local shortest-distance code. -/
@[expose] noncomputable def primedEntrySdpDecoder (u : ℕ → Fin 3) (j k : ℕ) : ℕ∞ :=
  primedEntrySdpCode u (primedEntrySdpLocalVertex primedEntryOuterVertex u j)
    (primedEntrySdpLocalVertex primedEntryGlueVertex u k)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The joint boundary-indexed SDP decoder is measurable. -/
theorem measurable_primedEntrySdpDecoder : Measurable primedEntrySdpDecoder := by
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro k
  have hc : Measurable (fun z : (ℕ → Fin 3) × (ℕ × ℕ) =>
      primedEntrySdpCode z.1 z.2.1 z.2.2) := by
    apply measurable_from_prod_countable_left
    intro ab
    have hid : @Measurable ℕ∞ ℕ∞ ⊤ inferInstance id := measurable_from_top
    exact hid.comp (measurable_primedEntrySdpCode ab.1 ab.2)
  exact hc.comp (measurable_id.prodMk
    ((measurable_sdpLocalVertex primedEntryOuterVertex j).prodMk
      (measurable_sdpLocalVertex primedEntryGlueVertex k)))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Reuse the distance-independent root and LL identifications at every outer index. -/
private theorem sdpOuterVertex_identification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) (j : ℕ) :
    PrimedEntryOuterVertexIdentification w h hb j := by
  rcases j with _ | j
  · exact primedEntryOuterVertexIdentification_zero_proved w h hb
  rcases j with _ | i
  · exact primedEntryOuterVertexIdentification_one_proved w h hb
  have hh := primedEntryOuterLLVertexIdentification_proved w h hb i
  filter_upwards [hh] with n hn
  obtain ⟨a, ha, ham⟩ := hn
  refine ⟨a, ?_, ham⟩
  simpa only [primedEntryOuterVertex, List.cons_append, List.nil_append,
    List.getElem?_cons_succ] using ha

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Injectivity fixes one local ID for each eventual outer endpoint. -/
private theorem sdpOuterVertex_fixed (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hb : BoundaryHitWitnesses w) (j : ℕ) :
    ∃ a, (∀ᶠ n in atTop,
      primedEntryOuterVertex (kmswStage (primedCode (primedSimInput w) h) n) j =
        some a) ∧ primedLimitVertexMap w h a = boundaryVertex w hb (-(j : ℤ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (sdpOuterVertex_identification w h hb j)
  obtain ⟨a, _, ham⟩ := hN N le_rfl
  refine ⟨a, ?_, ham⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨b, hb', hbm⟩ := hN n hn
  have he : b = a := (primedLimit_maps_injective_on_allocated w h).2
    ((primedLocalIds_eventually_allocated w h).2 b)
    ((primedLocalIds_eventually_allocated w h).2 a) (hbm.trans ham.symm)
  rwa [he] at hb'

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every boundary-indexed primed SDP is the minimum ambient first-entry length. -/
theorem primedEntrySdpDecoder_identification (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (j k : ℕ) :
    primedEntrySdpDecoder (primedCode (primedSimInput w) h) j k =
      leftLengthMin (leftPrimedEntryLengths w
        ⟨boundaryVertex w hb (-(j : ℤ))⟩ ⟨kmswBeta0Vertices w hfin hb k⟩) := by
  obtain ⟨a, ha, ham⟩ := sdpOuterVertex_fixed w h hb j
  have hg := primedEntryGlueVertex_eventually w h hfin hb k
  have hgm := primedEntryGlueVertexIdentification_proved w h hfin hb k
  rw [primedEntrySdpDecoder, sdpLocalVertex_eq _ _ _ a ha,
    sdpLocalVertex_eq _ _ _ _ hg, primedEntrySdpCode_identification, ham, hgm]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The primed SDP decoder exists with simultaneous finite-incidence and boundary witnesses. -/
theorem primedEntrySdpDecoderExists_proved : PrimedEntrySdpDecoderExists := by
  refine ⟨primedEntrySdpDecoder, measurable_primedEntrySdpDecoder, ?_⟩
  filter_upwards [iidCodeMeasure_ae_hasFlowLineHits] with ω h
  dsimp only
  intro hfin hb j k
  rw [hatLawPrimedCodes, dite_eq_left h, rightHat_boundaryIdTotal_eq ω hb]
  exact primedEntrySdpDecoder_identification _ h hfin hb j k

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted SDP decoder keeps the raw geodesic endpoints and unreachable top.
No decoder existence or raw identification is assumed here.
Proved downstream: `hattedLeftSeamSdpDecoderExists_proved`
(`Recursive/HattedLeftSeamSdpDecoderExists.lean`). -/
@[expose] def HattedLeftSeamSdpDecoderExists : Prop :=
  ∃ B : ThinCode → ℕ → ℕ → ℕ∞, Measurable B ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w) (q : D)
        (hw : (W q) = hatCodes w h), q.1 = integrateCodes (hatLawCodes ω) →
        ∀ k t, B (Tsdp .left (integrateCodes (hatLawCodes ω))) k t =
          leftLengthMin (leftHatClosedLengths w (closedLeftSdpEdges w h q)
            ⟨kmswBeta0Vertices w hfin hb k⟩
            ((leftAlongRawSdpGeodesic w h q hw).initial t).1)

end DirectedDistances.Recursive
