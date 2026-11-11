/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusMeasurableRelabel

/-! Finite cylinders and exact coordinate readers for the existing left decoder.
The decoder explicitly uses `Encodable.ofCountable`, not `encodableQuotient`;
minimal-representative locality cannot be inferred from its definition.
No complete-side locality or class-reader measurability is claimed here. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The existing edge IDs use the explicitly chosen
countable encoding, rather than the decidable-quotient encoding. -/
theorem lMinusCodeEdgeId_ofCountable {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (e : LMinusCodeGluedEdge r M) :
    lMinusCodeEdgeId r M e =
      @Encodable.encode _ (Encodable.ofCountable _) e := rfl

/-- Helper toward Lemma 5.5. Vertex IDs encode the raw quotient class,
using the explicitly chosen countable encoding before allocation. -/
theorem lMinusCodeVertexId_ofCountable {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (v : LMinusCodeGluedVertex r M) :
    lMinusCodeVertexId r M v =
      @Encodable.encode _ (Encodable.ofCountable _) v.1 := rfl

/-- Helper toward Lemma 5.5. A finite window retains both code blocks.
It records no stopping data absent from the presentation itself. -/
abbrev LMinusFiniteCodeWindow (N : ℕ) :=
  (Fin N → Fin 3) × (Fin N → Option FiniteThinMap)

/-- Helper toward Lemma 5.5. Both finite blocks with the hatted block
restricted to actual finite-half truncation values at each index. -/
abbrev LMinusFiniteTruncationWindow (N : ℕ) :=
  (Fin N → Fin 3) × ((i : Fin N) → Set.range (halfTruncate .left i.val))

/-- Helper toward Lemma 5.5. Reading a fixed finite window of both blocks. -/
@[expose] def lMinusFiniteCodeWindow {x : XDP}
    (N : ℕ) (r : LMinusSidePresentation x) : LMinusFiniteCodeWindow N :=
  (fun i => r.code.1 i, fun i => r.code.2 i)

/-- Helper toward Lemma 5.5. Finite windows with hatted values in their
actual finite-half truncation ranges form a countable space. No countability
instance for the entire `FiniteThinMap` carrier is assumed. -/
theorem countable_lMinusFiniteTruncationWindow (N : ℕ) :
    Countable (LMinusFiniteTruncationWindow N) := by
  let (i : Fin N) : Countable (Set.range (halfTruncate .left i.val)) :=
    (Set.countable_range (halfTruncate .left i.val)).to_subtype
  infer_instance

/-- Helper toward Lemma 5.5. The stopping value, its entire stopped prefix,
and a certified finite future window together have a countable value space. -/
theorem countable_lMinusStoppedWindow (N : ℕ) :
    Countable ((Σ t : ℕ, Fin t → Fin 3) × LMinusFiniteTruncationWindow N) := by
  let : Countable (LMinusFiniteTruncationWindow N) :=
    countable_lMinusFiniteTruncationWindow N
  infer_instance

/-- Helper toward Lemma 5.5. Each finite window is measurable. -/
theorem measurable_lMinusFiniteCodeWindow (x : XDP) (N : ℕ) :
    Measurable (lMinusFiniteCodeWindow (x := x) N) := by
  exact (measurable_pi_iff.mpr (fun (i : Fin N) => (measurable_pi_apply i.val).comp
    (measurable_lMinusSidePresentation_code x).fst)).prodMk
      (measurable_pi_iff.mpr (fun (i : Fin N) => (measurable_pi_apply i.val).comp
        (measurable_lMinusSidePresentation_code x).snd))

/-- Helper toward Lemma 5.5. Finite-window cylinders are measurable. -/
theorem measurableSet_lMinusFiniteCodeWindow (x : XDP) (N : ℕ)
    (c : LMinusFiniteCodeWindow N) :
    MeasurableSet {r : LMinusSidePresentation x | lMinusFiniteCodeWindow N r = c} :=
  (measurable_lMinusFiniteCodeWindow x N) (measurableSet_singleton c)

/-- Helper toward Lemma 5.5. The finite-window cylinders cover
the full presentation space, including unrealized presentations. -/
theorem iUnion_lMinusFiniteCodeWindow (x : XDP) (N : ℕ) :
    (⋃ c : LMinusFiniteCodeWindow N,
      {r : LMinusSidePresentation x | lMinusFiniteCodeWindow N r = c}) = Set.univ := by
  ext r
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨lMinusFiniteCodeWindow N r, rfl⟩

/-- Helper toward Lemma 5.5. Presentations whose first `N` hatted entries
are actual finite-half truncation values. This is a coordinate-range
restriction, without any geometric realization or locality assertion. -/
abbrev LMinusFiniteWindowDomain (x : XDP) (N : ℕ) :=
  {r : LMinusSidePresentation x //
    ∀ i : Fin N, r.code.2 i.val ∈ Set.range (halfTruncate .left i.val)}

/-- Helper toward Lemma 5.5. The finite coordinate-range domain is
measurable in the original presentation space. -/
theorem measurableSet_lMinusFiniteWindowDomain (x : XDP) (N : ℕ) :
    MeasurableSet {r : LMinusSidePresentation x |
      ∀ i : Fin N, r.code.2 i.val ∈ Set.range (halfTruncate .left i.val)} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (show MeasurableSet (Set.range (halfTruncate .left i.val)) from trivial).preimage
      ((measurable_pi_apply i.val).comp (measurable_lMinusSidePresentation_code x).snd))

/-- Helper toward Lemma 5.5. Every source-valid left presentation lies
in every finite hatted coordinate-range domain. -/
theorem lMinusCodeOf_hatted_mem_range {x : XDP}
    (q : LMinusPreimage x) (i : ℕ) :
    (lMinusCodeOf q).2 i ∈ Set.range (halfTruncate .left i) := by
  rw [← lMinusPreimage_hattedCode q,
    thinSideCode_coe x renewalTime renewalTime_positiveSuccessTime .left q.hattedCoherent]
  exact ⟨selectedCutSide x renewalTime .left
    (leastGoodCut x renewalTime renewalTime_positiveSuccessTime i q.hattedCoherent)
      q.hattedCoherent.1, rfl⟩

/-- Helper toward Lemma 5.5. On one common probability-one event every
hatted coordinate of the observed presentation lies in its countable
finite-half truncation range. -/
theorem ae_decodeLMinus_leftSideObsNonpos_hatted_mem_range
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ i : ℕ,
      (decodeLMinus x k (leftSideObsNonpos x k W)).code.2 i ∈
        Set.range (halfTruncate .left i) := by
  filter_upwards [ae_decodeLMinus_leftSideObsNonpos_classOption4_isSome x k hk]
    with W hW
  let r := decodeLMinus x k (leftSideObsNonpos x k W)
  have hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code := by
    by_contra hn
    have he := r.classOption4_eq_none_iff.mpr hn
    change r.classOption4.isSome = true at hW
    rw [he] at hW
    cases hW
  obtain ⟨q, hq⟩ := hq
  intro i
  change r.code.2 i ∈ Set.range (halfTruncate .left i)
  rw [← hq]
  exact lMinusCodeOf_hatted_mem_range q i

/-- Helper toward Lemma 5.5. The actual presentation law is concentrated
on the countable hatted coordinate ranges, simultaneously at every index.
Thus every certified finite-window domain is conull for this law. -/
theorem ae_lMinusSidePresentation_hatted_mem_range
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    ∀ᵐ r ∂(wholePlaneIIDCodeMeasure.map
      (fun W => decodeLMinus x k (leftSideObsNonpos x k W))),
      ∀ i : ℕ, r.code.2 i ∈ Set.range (halfTruncate .left i) := by
  have hM : MeasurableSet {r : LMinusSidePresentation x |
      ∀ i : ℕ, r.code.2 i ∈ Set.range (halfTruncate .left i)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i =>
      (show MeasurableSet (Set.range (halfTruncate .left i)) from trivial).preimage
        ((measurable_pi_apply i).comp (measurable_lMinusSidePresentation_code x).snd))
  exact (ae_map_iff (aemeasurable_decodeLMinus_leftSideObsNonpos x k) hM).mpr
    (ae_decodeLMinus_leftSideObsNonpos_hatted_mem_range x k hk)

/-- Helper toward Lemma 5.5. Read the countable window on its precise
coordinate-range domain, retaining all range certificates. -/
@[expose] def lMinusFiniteTruncationWindow {x : XDP} (N : ℕ)
    (r : LMinusFiniteWindowDomain x N) : LMinusFiniteTruncationWindow N :=
  (fun i => r.1.code.1 i.val, fun i => ⟨r.1.code.2 i.val, r.2 i⟩)

/-- Helper toward Lemma 5.5. Certified finite windows are measurable on
their coordinate-range domain. -/
theorem measurable_lMinusFiniteTruncationWindow (x : XDP) (N : ℕ) :
    Measurable (lMinusFiniteTruncationWindow (x := x) N) := by
  exact (measurable_pi_iff.mpr (fun (i : Fin N) =>
    ((measurable_pi_apply i.val).comp
      (measurable_lMinusSidePresentation_code x).fst).comp
        measurable_subtype_coe)).prodMk
    (measurable_pi_iff.mpr (fun (i : Fin N) =>
      (((measurable_pi_apply i.val).comp
        (measurable_lMinusSidePresentation_code x).snd).comp
          measurable_subtype_coe).subtype_mk))

/-- Helper toward Lemma 5.5. The countable certified-window cylinders are
measurable on their full coordinate-range domain. -/
theorem measurableSet_lMinusFiniteTruncationWindow (x : XDP) (N : ℕ)
    (c : LMinusFiniteTruncationWindow N) :
    MeasurableSet {r : LMinusFiniteWindowDomain x N |
      lMinusFiniteTruncationWindow N r = c} :=
  (measurable_lMinusFiniteTruncationWindow x N) (measurableSet_singleton c)

/-- Helper toward Lemma 5.5. The certified-window cylinders cover the
entire coordinate-range domain. -/
theorem iUnion_lMinusFiniteTruncationWindow (x : XDP) (N : ℕ) :
    (⋃ c : LMinusFiniteTruncationWindow N,
      {r : LMinusFiniteWindowDomain x N |
        lMinusFiniteTruncationWindow N r = c}) = Set.univ := by
  ext r
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨lMinusFiniteTruncationWindow N r, rfl⟩

/-- Helper toward Lemma 5.5. Every function of a fixed certified finite
window is measurable. No hypothesis about a decoded coordinate is used. -/
theorem measurable_lMinusFiniteTruncationWindow_comp {β : Type*}
    [MeasurableSpace β] (x : XDP) (N : ℕ)
    (f : LMinusFiniteTruncationWindow N → β) :
    Measurable (fun r : LMinusFiniteWindowDomain x N =>
      f (lMinusFiniteTruncationWindow N r)) := by
  let : Countable (LMinusFiniteTruncationWindow N) :=
    countable_lMinusFiniteTruncationWindow N
  exact (Measurable.of_discrete (f := f)).comp
    (measurable_lMinusFiniteTruncationWindow x N)

/-- Helper toward Lemma 5.5. Once an exterior raw boundary entry is
allocated by stage `N`, its value depends only on the first `N` primed
symbols. This conclusion concerns the raw label before quotient encoding. -/
theorem lMinusCodeExteriorBoundaryEdge_eq_of_prefix
    (p p' : ℕ → Fin 3) (N i : ℕ)
    (hprefix : ∀ j < N, p j = p' j)
    (hi : i < (0 :: (kmswStage p N).LL.reverse).length) :
    lMinusCodeExteriorBoundaryEdge p i = lMinusCodeExteriorBoundaryEdge p' i := by
  have hs := kmswStage_eq_of_prefix p p' N hprefix
  have hi' : i < (0 :: (kmswStage p' N).LL.reverse).length := by rwa [← hs]
  have h := lMinusCodeExteriorBoundaryEdge_stage p N i hi
  rw [hs, lMinusCodeExteriorBoundaryEdge_stage p' N i hi'] at h
  exact (Option.some.inj h).symm

/-- Helper toward Lemma 5.5. The orientation bit of each fully encoded
exterior boundary dart is constant, with future window bound zero. -/
theorem lMinusCodeSide4_boundary_snd (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (i : ℕ) :
    ((lMinusCodeSide4 x r q hf).boundary i).2 = true := rfl

/-- Helper toward Lemma 5.5. The boundary orientation-bit sequence is
measurable on the natural domain of the intrinsic code-side formula. -/
theorem measurable_lMinusCodeSide4_boundary_snd {Ω : Type*}
    [MeasurableSpace Ω] (x : XDP) (r : Ω → LMinusSidePresentation x)
    (q : Ω → Coherent x) (hf : ∀ ω, KMSWFiniteIncidence (r ω).code.1) (i : ℕ) :
    Measurable (fun ω => ((lMinusCodeSide4 x (r ω) (q ω) (hf ω)).boundary i).2) := by
  exact measurable_const

/-- Helper toward Lemma 5.5. The actual source-preimage decoder also has
constant reversed exterior orientation, independently of its numeric ID. -/
theorem lMinusPreimage_decodedSide4_boundary_snd {x : XDP}
    (q : LMinusPreimage x) (i : ℕ) :
    ((lMinusDecodedSide4 (W := q.W) (h := q.h) (k := q.k)
      (longest := q.longest) q.hτ q.hqMode q.hfin).boundary i).2 = true := rfl

/-- Helper toward Lemma 5.5. A strict inverse for the current dart IDs.
`decode₂` rejects numbers outside the encoding range; ordinary `decode`
only guarantees a left inverse on encoded inputs. -/
@[expose] noncomputable def lMinusCodeDartRead {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (d : ℕ × Bool) : Option (LMinusCodeGluedDart r M) :=
  (@Encodable.decode₂ _ (Encodable.ofCountable _) d.1).map
    (fun e => (e, d.2))

/-- Helper toward Lemma 5.5. Reading an intrinsic dart ID recovers its dart. -/
theorem lMinusCodeDartRead_id {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (d : LMinusCodeGluedDart r M) :
    lMinusCodeDartRead r M (lMinusCodeDartId r M d) = some d := by
  rcases d with ⟨e, s⟩
  change Option.map (fun a => (a, s))
    (@Encodable.decode₂ _ (Encodable.ofCountable _)
      (@Encodable.encode _ (Encodable.ofCountable _) e)) = some (e, s)
  rw [@Encodable.decode₂_encode _ (Encodable.ofCountable _) e]
  rfl

/-- Helper toward Lemma 5.5. Successful strict reading characterizes exactly
the given numeric dart ID, including its orientation bit. -/
theorem lMinusCodeDartRead_eq_some_iff {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (d : ℕ × Bool) (a : LMinusCodeGluedDart r M) :
    lMinusCodeDartRead r M d = some a ↔ lMinusCodeDartId r M a = d := by
  rcases d with ⟨n, s⟩
  rcases a with ⟨a, t⟩
  change Option.map (fun b => (b, s))
      (@Encodable.decode₂ _ (Encodable.ofCountable _) n) = some (a, t) ↔
    (@Encodable.encode _ (Encodable.ofCountable _) a, t) = (n, s)
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨b, hb, hbt⟩
    obtain ⟨rfl, hst⟩ := Prod.mk.inj hbt
    exact Prod.ext ((@Encodable.decode₂_eq_some _
      (Encodable.ofCountable _) n b).mp hb) hst.symm
  · intro h
    obtain ⟨ha, hts⟩ := Prod.mk.inj h
    exact ⟨a, (@Encodable.decode₂_eq_some _
      (Encodable.ofCountable _) n a).mpr ha, Prod.ext rfl hts.symm⟩

/-- Helper toward Lemma 5.5. At arbitrary numeric darts the corrected
rotation coordinate is the intrinsic splice on their strict readers. This
does not assert that the readers depend on finitely many code coordinates. -/
theorem lMinusCodeSide4_rotation_read_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (d e : ℕ × Bool) :
    (lMinusCodeSide4 x r q hf).rotation d e ↔
      ∃ a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q),
        lMinusCodeDartRead r _ d = some a ∧
        lMinusCodeDartRead r _ e = some b ∧
        lMinusCodeInitialSplicedRotation r q hf a = b := by
  simp_rw [lMinusCodeDartRead_eq_some_iff]
  rfl

/-- Helper toward Lemma 5.5. At arbitrary numeric darts the corrected
face-successor coordinate is the intrinsic retained-face relation on their
strict readers. Locality of those readers remains a separate obligation. -/
theorem lMinusCodeSide4_faceNext_read_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (d e : ℕ × Bool) :
    (lMinusCodeSide4 x r q hf).faceNext d e ↔
      ∃ a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q),
        lMinusCodeDartRead r _ d = some a ∧
        lMinusCodeDartRead r _ e = some b ∧
        lMinusCodeWholeFaceNext r q hf a b := by
  simp_rw [lMinusCodeDartRead_eq_some_iff]
  rfl















































































end DirectedDistances.PaperProofs.Section5
