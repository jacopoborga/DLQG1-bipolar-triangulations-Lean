module

public import DirectedDistances.Recursive.HLRSdpAssembly
public import DirectedDistances.Recursive.BusemannRightTruncationFormulaSdp
public import DirectedDistances.Recursive.HattedLeftSeamSdpDecoderExists
public import DirectedDistances.Recursive.BusemannLeftAlongCloseSdp
import DirectedDistances.KMSW.DirectedContainHat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory ProbabilityTheory Filter

local notation "ThinCode" => (ℕ → Option FiniteThinMap)
local notation "Tsdp" =>
  thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime
local notation "SdpDomain" =>
  selectedCutCoherentDomain XDP.sdp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A first-entry prefix uses only non-hatted geometric edges. -/
private theorem sdpFinalEntryEdges {w : ℕ → Fin 3} {x y : PresentVertex w}
    (p : Path x y)
    (hp : ∀ u ∈ p.vertices, u ≠ y → u ∉ leftHatVertices w) :
    ∀ e ∈ pathEdgeList p, ¬ MhatGeometricEdge w e := by
  have outside {a b : PresentVertex w} (r : Path a b)
      (hb : b ∉ leftHatVertices w) :
      ∀ e ∈ pathEdgeList r, ¬ MhatGeometricEdge w e := by
    induction r with
    | nil => simp [pathEdgeList]
    | @cons z b r e ih =>
      have hz : z ∉ leftHatVertices w := fun hz =>
        hb (leftHatVertices_closed hz e.toPath)
      intro f hf
      change f ∈ pathEdgeList r ++ [e.val] at hf
      rcases List.mem_append.mp hf with hf | hf
      · exact ih hz f hf
      · have heq := List.mem_singleton.mp hf
        subst f
        intro hg
        have hend := hg.2
        rw [e.property.2.2] at hend
        exact hb hend
  cases p with
  | nil => simp [pathEdgeList]
  | @cons z y p e =>
    have hzy : z ≠ y := by
      intro he
      subst y
      have hz := presentVertex_acyclic w z e.toPath
      simp only [Path.length_toPath] at hz
      omega
    have hz := hp z ((Path.mem_vertices_cons p e).mpr
      (Or.inl p.end_mem_vertices)) hzy
    intro f hf
    change f ∈ pathEdgeList p ++ [e.val] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact outside p hz f hf
    · have heq := List.mem_singleton.mp hf
      subst f
      intro hg
      have hstart := hg.1
      rw [e.property.2.1] at hstart
      exact hz hstart

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Exact first-entry decomposition for paths confined to the closed left side. -/
theorem leftClosedSdpLengths_beta (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (q : SdpDomain)
    {x y : PresentVertex w} (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    leftClosedSdpSidePathLengths w (closedLeftSdpEdges w h q) x y =
      {n | ∃ k, ∃ a ∈ leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb k⟩,
        ∃ b ∈ leftHatClosedLengths w (closedLeftSdpEdges w h q)
          ⟨kmswBeta0Vertices w hfin hb k⟩ y, n = a + b} := by
  ext n
  constructor
  · rintro ⟨p, rfl, hp⟩
    obtain ⟨k, a, b, heq, ha, hb'⟩ := leftHat_firstEntry_beta w hfin hb p hx hy
    have ha' : ∀ u ∈ a.vertices, u ≠ (⟨kmswBeta0Vertices w hfin hb k⟩ :
        PresentVertex w) → u ∉ leftHatVertices w := by
      intro u hu hne
      exact ha u hu (fun hid => hne (congrArg PresentVertex.mk hid))
    refine ⟨k, a.length, ⟨a, rfl, ha'⟩, b.length, ⟨b, rfl, hb', ?_⟩, ?_⟩
    · intro e he
      apply hp e
      rw [heq, pathEdgeList_comp]
      exact List.mem_append.mpr (Or.inr he)
    · simp only [heq, Path.length_comp]
  · rintro ⟨k, a, ⟨p, hp, ha⟩, b, ⟨r, hr, _, he⟩, rfl⟩
    refine ⟨p.comp r, by simp only [Path.length_comp, hp, hr], ?_⟩
    intro e he'
    rw [pathEdgeList_comp] at he'
    exact (List.mem_append.mp he').elim
      (fun hep => Or.inl (sdpFinalEntryEdges p ha e hep)) (he e)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An attained least natural length identifies the extended minimum. -/
private theorem sdpFinalMin_least (s : Set ℕ) {n : ℕ} (hn : IsLeast s n) :
    leftLengthMin s = (n : ℕ∞) := by
  rw [leftLengthMin, dite_eq_left ⟨n, hn.1⟩]
  exact congrArg (fun m : ℕ => (m : ℕ∞))
    (le_antisymm (Nat.sInf_le hn.1) (hn.2 (Nat.sInf_mem ⟨n, hn.1⟩)))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A lower bound on attainable sums bounds the sum of extended minima, including empty -/
private theorem sdpFinalMin_add_ge (a b : Set ℕ) (n : ℕ)
    (hn : ∀ i ∈ a, ∀ j ∈ b, n ≤ i + j) :
    (n : ℕ∞) ≤ leftLengthMin a + leftLengthMin b := by
  classical
  by_cases ha : a.Nonempty
  · by_cases hb : b.Nonempty
    · rw [leftLengthMin, dite_eq_left ha, leftLengthMin, dite_eq_left hb,
        ← ENat.natCast_add]
      exact ENat.natCast_le_natCast.mpr (hn _ (Nat.sInf_mem ha) _ (Nat.sInf_mem hb))
    · rw [leftLengthMin, dite_eq_left ha, leftLengthMin, dite_eq_right hb]
      simp only [add_top, le_top]
  · rw [leftLengthMin, dite_eq_right ha]
    simp only [top_add, le_top]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The attained closed-left minimum is the countable infimum of primed-entry and hatted
closed-left minima. All beta indices are retained; unreachable terms stay top. -/
theorem leftClosedMinimumSdp_beta (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (q : SdpDomain)
    {x y : PresentVertex w} (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w)
    {n : ℕ}
    (hn : IsLeast (leftClosedSdpSidePathLengths w (closedLeftSdpEdges w h q) x y) n) :
    (⨅ k : ℕ,
      leftLengthMin (leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb k⟩) +
      leftLengthMin (leftHatClosedLengths w (closedLeftSdpEdges w h q)
        ⟨kmswBeta0Vertices w hfin hb k⟩ y)) = (n : ℕ∞) := by
  classical
  let a := fun k => leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb k⟩
  let b := fun k => leftHatClosedLengths w (closedLeftSdpEdges w h q)
    ⟨kmswBeta0Vertices w hfin hb k⟩ y
  have hdecomp := leftClosedSdpLengths_beta w h hfin hb q hx hy
  have hbound (k : ℕ) (i : ℕ) (hi : i ∈ a k) (j : ℕ) (hj : j ∈ b k) : n ≤ i + j := by
    apply hn.2
    rw [hdecomp]
    exact ⟨k, i, hi, j, hj, rfl⟩
  change (⨅ k, leftLengthMin (a k) + leftLengthMin (b k)) = _
  apply le_antisymm
  · have hmem := hn.1
    rw [hdecomp] at hmem
    obtain ⟨k, i, hi, j, hj, hnij⟩ := hmem
    have hia : IsLeast (a k) i := ⟨hi, by
      intro l hl
      have hh := hbound k l hl j hj
      omega⟩
    have hjb : IsLeast (b k) j := ⟨hj, by
      intro l hl
      have hh := hbound k i hi l hl
      omega⟩
    calc
      (⨅ k, leftLengthMin (a k) + leftLengthMin (b k)) ≤
          leftLengthMin (a k) + leftLengthMin (b k) := iInf_le _ k
      _ = (n : ℕ∞) := by
        rw [sdpFinalMin_least _ hia, sdpFinalMin_least _ hjb,
          ← ENat.natCast_add, ← hnij]
  · exact le_iInf (fun k => sdpFinalMin_add_ge _ _ n (hbound k))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Measurable reconstruction for the ℕ-indexed left and right profiles j ↦ V(−j), j ↦ V(j).
The top-to-natural conversion is only used after proving a finite value on the -/
@[expose] noncomputable def leftLocalitySdpDecoder
    (A : (ℕ → Fin 3) → ℕ → ℕ → ℕ∞)
    (B : ThinCode → ℕ → ℕ → ℕ∞) (z : ThinCode × (ℕ → Fin 3)) (j : ℕ) : ℤ :=
  if j = 0 then 0 else eventualIntValue 0 (fun t =>
    Int.ofNat ((⨅ k : ℕ, A z.2 j k + B z.1 k t).toNat) - (t : ℤ))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Countable infima and the eventual-value selector give measurable reconstruction. -/
theorem measurable_leftLocalitySdpDecoder
    {A : (ℕ → Fin 3) → ℕ → ℕ → ℕ∞}
    {B : ThinCode → ℕ → ℕ → ℕ∞} (hA : Measurable A) (hB : Measurable B) :
    Measurable (leftLocalitySdpDecoder A B) := by
  let : TopologicalSpace ℕ∞ := inferInstanceAs (TopologicalSpace (WithTop ℕ))
  have : OrderTopology ℕ∞ := inferInstanceAs (OrderTopology (WithTop ℕ))
  have : SecondCountableTopology ℕ∞ :=
    inferInstanceAs (SecondCountableTopology (WithTop ℕ))
  have : BorelSpace ℕ∞ := ⟨borel_eq_top_of_countable.symm⟩
  apply Measurable.of_eval
  intro j
  unfold leftLocalitySdpDecoder
  split_ifs
  · exact measurable_const
  · apply measurable_eventualIntValue
    intro t
    have hs : Measurable (fun z : ThinCode × (ℕ → Fin 3) =>
        ⨅ k : ℕ, A z.2 j k + B z.1 k t) := by
      apply Measurable.iInf
      intro k
      exact (measurable_of_countable (fun p : ℕ∞ × ℕ∞ => p.1 + p.2)).comp
        (((measurable_pi_apply k).comp
          ((measurable_pi_apply j).comp (hA.comp measurable_snd))).prodMk
          ((measurable_pi_apply t).comp
            ((measurable_pi_apply k).comp (hB.comp measurable_fst))))
    exact ((measurable_of_countable (fun v : ℕ∞ => Int.ofNat v.toNat)).comp
      hs).sub measurable_const

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Strictly negative boundary vertices are outside the root-reachable submap. -/
private theorem sdpFinalNegativeOutside (ω : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) (j : ℕ) (hj : 1 ≤ j) :
    (⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩ : PresentVertex (fun i => ω (i + 1))) ∉
      leftHatVertices (fun i => ω (i + 1)) := by
  rw [rightHat_boundaryIdTotal_eq ω hb]
  have hne : boundaryVertex (fun i => ω (i + 1)) hb (-(j : ℤ)) ≠ 0 := by
    intro he
    have hh := boundaryVertex_injective _ hb (he.trans (boundaryVertex_zero _ hb).symm)
    omega
  have noReach (v : PresentVertex (fun i => ω (i + 1))) (hv : v.id ≠ 0)
      (hno : ∀ e, EdgePresent (fun i => ω (i + 1)) e →
        edgeEast (fun i => ω (i + 1)) e ≠ v.id) :
      ¬ Reachable (⟨0⟩ : PresentVertex (fun i => ω (i + 1))) v := by
    rintro ⟨p⟩
    cases p with
    | nil => exact hv rfl
    | cons p e => exact hno e.val e.property.1 e.property.2.2
  exact noReach _ hne (fun e he =>
    boundaryVertex_nonpos_no_incoming _ hb (by omega) e he)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Almost surely the late closed-left seam minimum is the beta-indexed countable infimum,
with its finite Busemann difference. No bound on contributing indices is required. -/
theorem leftAlongClosedMinimumSdp_beta_ae :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w) (q : SdpDomain) (hw : (W q) = hatCodes w h),
        q.1 = integrateCodes (hatLawCodes ω) ∧
        ∀ j : ℕ, 1 ≤ j → ∃ c : ℤ,
          busemannSDPMeasurableVersion ω (-(j : ℤ)) = c ∧
          ∀ᶠ t in atTop, ∃ n : ℕ,
            IsLeast (leftClosedSdpSidePathLengths w (closedLeftSdpEdges w h q)
              ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩
              ((leftAlongRawSdpGeodesic w h q hw).initial t).1) n ∧
            (⨅ k : ℕ, leftLengthMin (leftPrimedEntryLengths w
              ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩ ⟨kmswBeta0Vertices w hfin hb k⟩) +
              leftLengthMin (leftHatClosedLengths w (closedLeftSdpEdges w h q)
                ⟨kmswBeta0Vertices w hfin hb k⟩
                ((leftAlongRawSdpGeodesic w h q hw).initial t).1)) = (n : ℕ∞) ∧
            (n : ℤ) - (t : ℤ) = c := by
  filter_upwards [leftAlongSdpBusemannFormulaAE_proved,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryBusemannSDP_existsUnique]
    with ω hf hfinite hω
  obtain ⟨h, q, hw, hq, hf⟩ := hf
  obtain ⟨hb, X, hX, huniq⟩ := hω
  have hfin : hatLimitFiniteIncidence (fun i => ω (i + 1)) := by
    intro v
    exact hfinite v
  refine ⟨h, hfin, hb, q, hw, hq, fun j hj => ?_⟩
  obtain ⟨c, hc, _, hlate⟩ := hf j hj
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlate] with t ht
  obtain ⟨n, hn, _, hnt⟩ := ht
  have hy : ((leftAlongRawSdpGeodesic _ h q hw).initial t).1 ∈
      leftHatVertices (fun i => ω (i + 1)) := by
    rw [leftAlongRawSdpGeodesic_vertex]
    apply alloc_reachable (hatLimitExplicitInput _ h)
    rw [← hw]
    exact kmswVertexAllocated_all (W q)
      ((sourceAncestorPath XDP.sdp renewalTime renewalTime_positiveSuccessTime q).initial t).1
  exact ⟨n, hn,
    leftClosedMinimumSdp_beta _ h hfin hb q (sdpFinalNegativeOutside ω hb j hj) hy hn,
    hnt⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The proved decoders reconstruct the left member of the ℕ-indexed left and right profiles -/
theorem leftBusemannSdpLocality_proved : LeftBusemannSdpLocality := by
  obtain ⟨A, hAm, hA⟩ := primedEntrySdpDecoderExists_proved
  obtain ⟨B, hBm, hB⟩ := hattedLeftSeamSdpDecoderExists_proved
  refine ⟨leftLocalitySdpDecoder A B, measurable_leftLocalitySdpDecoder hAm hBm, ?_⟩
  filter_upwards [hA, hB, leftAlongClosedMinimumSdp_beta_ae] with ω hA hB hf
  obtain ⟨h, hfin, hb, q, hw, hq, hf⟩ := hf
  funext j
  by_cases hj : j = 0
  · subst j
    simpa [leftLocalitySdpDecoder] using
      busemannSDPMeasurableVersion_zero ω
  · obtain ⟨c, hc, hlate⟩ := hf j (by omega)
    rw [hc]
    unfold leftLocalitySdpDecoder
    rw [ite_eq_right hj]
    symm
    apply eventualIntValue_eq
    filter_upwards [hlate] with t ht
    obtain ⟨n, _, hsum, hnt⟩ := ht
    have hs : (⨅ k : ℕ, A (hatLawPrimedCodes ω) j k +
        B (Tsdp .left (integrateCodes (hatLawCodes ω))) k t) = (n : ℕ∞) := by
      simpa only [hA hfin hb j, hB h hfin hb q hw hq] using hsum
    rw [hs, ENat.toNat_natCast]
    exact hnt

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Independence of the ℕ-indexed left and right profiles j ↦ V(−j), j ↦ V(j). -/
theorem hLR_sdp_proved :
    IndepFun (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (-(j : ℤ)))
      (fun ω (j : ℕ) => busemannSDPMeasurableVersion ω (j : ℤ)) iidCodeMeasure :=
  hLR_sdp_of_localities rightBusemannSdpLocality_proved leftBusemannSdpLocality_proved

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Independent SDP increments from the ℕ-indexed left and right profiles j ↦ V(−j), j ↦ V(j). -/
theorem sdpIncrements_iIndep_proved :
    iIndepFun
      (fun k ω => SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω)
      iidCodeMeasure :=
  sdpIncrements_iIndep_of_localities
    rightBusemannSdpLocality_proved leftBusemannSdpLocality_proved

end DirectedDistances.Recursive
