module

public import DirectedDistances.Recursive.BusemannLeftAlongClose
public import DirectedDistances.Recursive.HLRLdpAssembly
import DirectedDistances.KMSW.DirectedContainHat
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "ThinCode" => (ℕ → Option FiniteThinMap)
local notation "Tldp" =>
  thinSideCode XDP.ldp renewalTime renewalTime_positiveSuccessTime
local notation "RightDomain" =>
  selectedCutCoherentDomain XDP.ldp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The canonical Borel measurable space on finite lengths with an unreachable bottom. -/
instance leftLocalityWithBotMeasurableSpace : MeasurableSpace (WithBot ℕ) := borel _

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The finite-length measurable space is its order-topology Borel space. -/
instance leftLocalityWithBotBorelSpace : BorelSpace (WithBot ℕ) := ⟨rfl⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Lengths in the intersection of the induced hatted map and the closed left side.
Both vertex confinement and the original raw edge identities are retained. -/
@[expose] def leftHatClosedLengths (w : ℕ → Fin 3) (E : Set ℕ)
    (v y : PresentVertex w) : Set ℕ :=
  {n | ∃ p : Path v y, p.length = n ∧
    (∀ u ∈ p.vertices, u ∈ leftHatVertices w) ∧ ∀ e ∈ pathEdgeList p, e ∈ E}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A first-entry prefix uses only non-hatted geometric edges. -/
private theorem entryEdges {w : ℕ → Fin 3} {x y : PresentVertex w}
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
theorem leftClosedLengths_beta (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (q : RightDomain)
    {x y : PresentVertex w} (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    leftClosedSidePathLengths w (closedLeftEdges w h q) x y =
      {n | ∃ k, ∃ a ∈ leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb k⟩,
        ∃ b ∈ leftHatClosedLengths w (closedLeftEdges w h q)
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
      (fun hep => Or.inl (entryEdges p ha e hep)) (he e)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An attained maximum identifies the supremum, preserving bottom for empty sets. -/
private theorem lengthSup_greatest (s : Set ℕ) {n : ℕ} (hn : IsGreatest s n) :
    leftLengthSup s = (n : WithBot ℕ) := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨n, hn.1, rfl⟩, by
    rintro z ⟨k, hk, rfl⟩
    exact WithBot.coe_le_coe.mpr (hn.2 hk)⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite length sets have a sum of suprema bounded by every bound on attainable sums. -/
private theorem lengthSup_add_le (a b : Set ℕ) (ha : a.Finite) (hb : b.Finite)
    (N : ℕ) (hN : ∀ i ∈ a, ∀ j ∈ b, i + j ≤ N) :
    leftLengthSup a + leftLengthSup b ≤ (N : WithBot ℕ) := by
  classical
  by_cases hna : a.Nonempty
  · by_cases hnb : b.Nonempty
    · have hma : IsGreatest a (sSup a) :=
        ⟨hna.csSup_mem ha, fun _ hi => le_csSup ha.bddAbove hi⟩
      have hmb : IsGreatest b (sSup b) :=
        ⟨hnb.csSup_mem hb, fun _ hj => le_csSup hb.bddAbove hj⟩
      rw [lengthSup_greatest a hma, lengthSup_greatest b hmb]
      exact WithBot.coe_le_coe.mpr (hN _ hma.1 _ hmb.1)
    · have he : b = ∅ := Set.not_nonempty_iff_eq_empty.mp hnb
      simp only [he, leftLengthSup, Set.image_empty, csSup_empty, WithBot.add_bot, bot_le]
  · have he : a = ∅ := Set.not_nonempty_iff_eq_empty.mp hna
    simp only [he, leftLengthSup, Set.image_empty, csSup_empty, WithBot.bot_add, bot_le]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The attained closed-left maximum is the beta-indexed sum of the two restricted maxima.
Finite incidence bounds all length sets; no unreachable distance is treated as zero. -/
theorem leftClosedMaximum_beta (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (q : RightDomain)
    {x y : PresentVertex w} (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w)
    {n : ℕ} (hn : IsGreatest (leftClosedSidePathLengths w (closedLeftEdges w h q) x y) n) :
    (⨆ k : ℕ,
      leftLengthSup (leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb k⟩) +
      leftLengthSup (leftHatClosedLengths w (closedLeftEdges w h q)
        ⟨kmswBeta0Vertices w hfin hb k⟩ y)) = (n : WithBot ℕ) := by
  classical
  let a := fun k => leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb k⟩
  let b := fun k => leftHatClosedLengths w (closedLeftEdges w h q)
    ⟨kmswBeta0Vertices w hfin hb k⟩ y
  have hdecomp := leftClosedLengths_beta w h hfin hb q hx hy
  have hbound (k : ℕ) (i : ℕ) (hi : i ∈ a k) (j : ℕ) (hj : j ∈ b k) : i + j ≤ n := by
    apply hn.2
    rw [hdecomp]
    exact ⟨k, i, hi, j, hj, rfl⟩
  have hfinite (u v : PresentVertex w) : (pathLengths u v).Finite :=
    pathLengths_finite_of_bddAbove (present_pathLengths_bddAbove w hfin u v)
  have hupper (k : ℕ) : leftLengthSup (a k) + leftLengthSup (b k) ≤ (n : WithBot ℕ) := by
    apply lengthSup_add_le _ _ ((hfinite x ⟨kmswBeta0Vertices w hfin hb k⟩).subset ?_)
      ((hfinite ⟨kmswBeta0Vertices w hfin hb k⟩ y).subset ?_) n
      (hbound k)
    · rintro i ⟨p, hp, _⟩
      exact ⟨p, hp⟩
    · rintro i ⟨p, hp, _⟩
      exact ⟨p, hp⟩
  change (⨆ k, leftLengthSup (a k) + leftLengthSup (b k)) = _
  apply le_antisymm (ciSup_le hupper)
  have hmem := hn.1
  rw [hdecomp] at hmem
  obtain ⟨k, i, hi, j, hj, hnij⟩ := hmem
  have hia : IsGreatest (a k) i := ⟨hi, by
    intro l hl
    have hh := hbound k l hl j hj
    omega⟩
  have hjb : IsGreatest (b k) j := ⟨hj, by
    intro l hl
    have hh := hbound k i hi l hl
    omega⟩
  apply le_ciSup_of_le ⟨_, by rintro z ⟨k, rfl⟩; exact hupper k⟩ k
  rw [lengthSup_greatest _ hia, lengthSup_greatest _ hjb, hnij]
  exact le_rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The beta prefix is a genuine directed path of length equal to its index. -/
private theorem betaPrefix (w : ℕ → Fin 3) (hfin : hatLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (k : ℕ) :
    ∃ p : Path (⟨0⟩ : PresentVertex w) ⟨kmswBeta0Vertices w hfin hb k⟩,
      p.length = k := by
  induction k with
  | zero => exact ⟨Path.nil, rfl⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih
    have ht : edgeWest w (kmswBeta0Stream w hfin hb k).1 =
        kmswBeta0Vertices w hfin hb k := by
      cases k with
      | zero => exact kmswBeta0Stream_start w hfin hb
      | succ k => exact kmswBeta0Stream_chain w hfin hb k
    let e : (⟨kmswBeta0Vertices w hfin hb k⟩ : PresentVertex w) ⟶
        ⟨kmswBeta0Vertices w hfin hb (k + 1)⟩ :=
      ⟨(kmswBeta0Stream w hfin hb k).1,
        (kmswBeta0Stream w hfin hb k).property, ht, rfl⟩
    exact ⟨p.cons e, by simp only [Path.length_cons, hp]⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Only indices at most the seam time can have any hatted suffix to the target.
This gives an explicit finite support bound, independent of the entry vertex. -/
theorem leftBetaSeam_index_le (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (q : RightDomain)
    (hw : (W q) = hatCodes w h) (k t : ℕ)
    (hr : Reachable (⟨kmswBeta0Vertices w hfin hb k⟩ : PresentVertex w)
      ((leftAlongRawGeodesic w h q hw).initial t).1) : k ≤ t := by
  obtain ⟨p, hp⟩ := betaPrefix w hfin hb k
  obtain ⟨r⟩ := hr
  have hh := leftAlongRawGeodesic_initial_isLongest w h q hw t (p.comp r)
  rw [Path.length_comp, hp, (leftAlongRawGeodesic w h q hw).prefix_length] at hh
  omega

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The contributing beta indices lie in the finite interval from zero through the seam time. -/
theorem leftHatClosed_contributors_finite (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (q : RightDomain)
    (hw : (W q) = hatCodes w h) (t : ℕ) :
    {k : ℕ | (leftHatClosedLengths w (closedLeftEdges w h q)
      ⟨kmswBeta0Vertices w hfin hb k⟩
      ((leftAlongRawGeodesic w h q hw).initial t).1).Nonempty}.Finite := by
  apply (Set.finite_Iic t).subset
  rintro k ⟨n, p, _, _⟩
  exact leftBetaSeam_index_le w h hfin hb q hw k t p.reachable

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Both premises are proved downstream: `primedEntryDecoderExists_proved`
(`Recursive/HLRLdpFinal.lean`) and `hattedLeftSeamDecoderExists_proved`
(`Recursive/HattedLeftSeamDecoderExists.lean`). This proposition defines the primed
entry decoder premise. Witnesses range over the actual shifted raw code.
The universal proof witnesses are harmless: all are propositions and hence proof irrelevant.
Almost-sure existence of these witnesses is already proved by the Busemann input. -/
@[expose] def PrimedEntryDecoderExists : Prop :=
  ∃ A : (ℕ → Fin 3) → ℕ → ℕ → WithBot ℕ, Measurable A ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ (hfin : hatLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w), ∀ j k,
        A (hatLawPrimedCodes ω) j k = leftLengthSup
          (leftPrimedEntryLengths w ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩
            ⟨kmswBeta0Vertices w hfin hb k⟩)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Both premises are proved downstream: `primedEntryDecoderExists_proved`
(`Recursive/HLRLdpFinal.lean`) and `hattedLeftSeamDecoderExists_proved`
(`Recursive/HattedLeftSeamDecoderExists.lean`). This proposition defines the hatted
closed-left seam decoder premise. Its carrier and integrated code are explicitly
identified; the target is the actual raw geodesic seam, not a boundary proxy. -/
@[expose] def HattedLeftSeamDecoderExists : Prop :=
  ∃ B : ThinCode → ℕ → ℕ → WithBot ℕ, Measurable B ∧
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w) (q : RightDomain)
        (hw : (W q) = hatCodes w h), q.1 = integrateCodes (hatLawCodes ω) →
        ∀ k t, B (Tldp .left (integrateCodes (hatLawCodes ω))) k t =
          leftLengthSup (leftHatClosedLengths w (closedLeftEdges w h q)
            ⟨kmswBeta0Vertices w hfin hb k⟩
            ((leftAlongRawGeodesic w h q hw).initial t).1)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Totalized measurable reconstruction. The zero at bottom is only off-domain junk;
the reconstruction theorem uses attained finite maxima before converting to integers. -/
@[expose] noncomputable def leftLocalityDecoder
    (A : (ℕ → Fin 3) → ℕ → ℕ → WithBot ℕ)
    (B : ThinCode → ℕ → ℕ → WithBot ℕ) (z : ThinCode × (ℕ → Fin 3))
    (j : ℕ) : ℤ :=
  if j = 0 then 0 else eventualIntValue 0 (fun t =>
    Int.ofNat ((⨆ k : ℕ, A z.2 j k + B z.1 k t).unbotD 0) - (t : ℤ))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Countable suprema and the eventual-value selector give measurability on code space. -/
theorem measurable_leftLocalityDecoder
    {A : (ℕ → Fin 3) → ℕ → ℕ → WithBot ℕ}
    {B : ThinCode → ℕ → ℕ → WithBot ℕ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (leftLocalityDecoder A B) := by
  apply Measurable.of_eval
  intro j
  unfold leftLocalityDecoder
  split_ifs
  · exact measurable_const
  · apply measurable_eventualIntValue
    intro t
    have hs : Measurable (fun z : ThinCode × (ℕ → Fin 3) =>
        ⨆ k : ℕ, A z.2 j k + B z.1 k t) := by
      apply Measurable.iSup
      intro k
      exact ((measurable_pi_apply k).comp
        ((measurable_pi_apply j).comp (hA.comp measurable_snd))).add
        ((measurable_pi_apply t).comp
          ((measurable_pi_apply k).comp (hB.comp measurable_fst)))
    exact ((measurable_of_countable (fun v : WithBot ℕ => Int.ofNat (v.unbotD 0))).comp
      hs).sub measurable_const

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Strictly negative boundary vertices are outside the root-reachable submap. -/
private theorem negativeOutside (ω : ℕ → Fin 3)
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
Almost surely, every positive negative-boundary index has the stated late-seam
closed-left decomposition, attained maximum and Busemann difference on common carriers.
The finite support bound for each target is `leftBetaSeam_index_le`. -/
theorem leftAlongClosedMaximum_beta_ae :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w) (q : RightDomain) (hw : (W q) = hatCodes w h),
        q.1 = integrateCodes (hatLawCodes ω) ∧
        ∀ j : ℕ, 1 ≤ j → ∃ c : ℤ,
          busemannLDPMeasurableVersion ω (-(j : ℤ)) = c ∧
          ∀ᶠ t in atTop, ∃ n : ℕ,
            IsGreatest (leftClosedSidePathLengths w (closedLeftEdges w h q)
              ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩
              ((leftAlongRawGeodesic w h q hw).initial t).1) n ∧
            (⨆ k : ℕ, leftLengthSup (leftPrimedEntryLengths w
              ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩ ⟨kmswBeta0Vertices w hfin hb k⟩) +
              leftLengthSup (leftHatClosedLengths w (closedLeftEdges w h q)
                ⟨kmswBeta0Vertices w hfin hb k⟩
                ((leftAlongRawGeodesic w h q hw).initial t).1)) = (n : WithBot ℕ) ∧
            (n : ℤ) - (t : ℤ) = c := by
  filter_upwards [leftAlongBusemannFormulaAE_proved,
    iidCodes_ae_boundaryBusemannLDP_existsUnique] with ω hf hω
  obtain ⟨h, q, hw, hq, hf⟩ := hf
  obtain ⟨hfin, hb, X, hX, huniq⟩ := hω
  refine ⟨h, hfin, hb, q, hw, hq, fun j hj => ?_⟩
  obtain ⟨c, hc, _, hlate⟩ := hf j hj
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlate] with t ht
  obtain ⟨n, hn, _, hnt⟩ := ht
  have hy : ((leftAlongRawGeodesic _ h q hw).initial t).1 ∈
      leftHatVertices (fun i => ω (i + 1)) := by
    rw [leftAlongRawGeodesic_vertex]
    apply alloc_reachable (hatLimitExplicitInput _ h)
    rw [← hw]
    exact kmswVertexAllocated_all (W q)
      ((sourceAncestorPath XDP.ldp renewalTime renewalTime_positiveSuccessTime q).initial t).1
  exact ⟨n, hn, leftClosedMaximum_beta _ h hfin hb q (negativeOutside ω hb j hj) hy hn,
    hnt⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The two decoder premises imply the left Busemann locality needed for independence.
Both premises are proved downstream: `primedEntryDecoderExists_proved`
(`Recursive/HLRLdpFinal.lean`) and `hattedLeftSeamDecoderExists_proved`
(`Recursive/HattedLeftSeamDecoderExists.lean`). They are passed explicitly here. -/
theorem leftBusemannLdpLocality_of_decoders (hA : PrimedEntryDecoderExists)
    (hB : HattedLeftSeamDecoderExists) : LeftBusemannLdpLocality := by
  obtain ⟨A, hAm, hA⟩ := hA
  obtain ⟨B, hBm, hB⟩ := hB
  refine ⟨leftLocalityDecoder A B, measurable_leftLocalityDecoder hAm hBm, ?_⟩
  filter_upwards [hA, hB, leftAlongClosedMaximum_beta_ae] with ω hA hB hf
  obtain ⟨h, hfin, hb, q, hw, hq, hf⟩ := hf
  funext j
  by_cases hj : j = 0
  · subst j
    simpa [leftLocalityDecoder] using
      (busemannLDPProfiles_zero_agree ω).1
  · obtain ⟨c, hc, hlate⟩ := hf j (by omega)
    rw [hc]
    unfold leftLocalityDecoder
    rw [ite_eq_right hj]
    symm
    apply eventualIntValue_eq
    filter_upwards [hlate] with t ht
    obtain ⟨n, _, hsum, hnt⟩ := ht
    have hs : (⨆ k : ℕ, A (hatLawPrimedCodes ω) j k +
        B (Tldp .left (integrateCodes (hatLawCodes ω))) k t) = (n : WithBot ℕ) := by
      simpa only [hA hfin hb j, hB h hfin hb q hw hq] using hsum
    rw [hs]
    exact hnt

end DirectedDistances.Recursive
