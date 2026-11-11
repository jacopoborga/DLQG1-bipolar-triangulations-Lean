/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWShiftAllTimes
public import DirectedDistances.KMSW.StageDirectedMapPathLengths
public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLaw
import DirectedDistances.PlanarMap.FiniteXDPDistances
import DirectedDistances.Paper.Section1.CellLDP
import DirectedDistances.RandomWalk.IIDWalkMaximalTailBound

/-! # Segment paths in the stopped Boltzmann map

Deterministic helpers toward Lemma 7.11 (`lem-boltzmann-ldp-lower`,
a shifted KMSW stage embeds in the corresponding global stage. Before the
right-coordinate hit, it therefore embeds in the stopped stage at `τ - 1`.
The proved source and sink connectivity of the finite bipolar map extends
this path to a source-to-sink path. No connectivity premise is assumed.

`ldpLengthBase` is natural-valued because the finite bipolar map has a
nonempty source-to-sink path family. Its casts below agree with the
`WithBot ℕ` convention, in which unreachable pairs have value `⊥`. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver
open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 7.11; not a paper result. The shifted finite stage
maps into the global stage at the segment's terminal time, preserving each
present edge and its endpoints. -/
@[expose] def ldpLowerSegmentToStage (w : ℕ → Fin 3) (T N : ℕ) :
    Prefunctor (StagePresentVertex (fun i => w (T + i)) N)
      (StagePresentVertex w (T + N)) where
  obj v := ⟨kmswShiftVertexMapAll w T N v.id⟩
  map {_ _} e := by
    have h := kmswShift_present_edge_stage w T N e.val
      e.property.1 e.property.2.1 N le_rfl
    exact ⟨kmswShiftEdgeMapAll w T N e.val, h.1, h.2.1,
      h.2.2.1.trans (congrArg (kmswShiftVertexMapAll w T N) e.property.2.2.1),
      h.2.2.2.trans (congrArg (kmswShiftVertexMapAll w T N) e.property.2.2.2)⟩

/-- Helper toward Lemma 7.11; not a paper result. Segment inclusion preserves
the number of arrows, including parallel edges. -/
theorem ldpLowerSegmentToStage_length (w : ℕ → Fin 3) (T N : ℕ)
    {a b : StagePresentVertex (fun i => w (T + i)) N} (p : Path a b) :
    ((ldpLowerSegmentToStage w T N).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem segmentPath_endpoints_allocated (w : ℕ → Fin 3) (n : ℕ)
    {a b : StagePresentVertex w n} (p : Path a b) (hp : 0 < p.length) :
    a.id < (kmswStage w n).nextVertex ∧ b.id < (kmswStage w n).nextVertex := by
  induction p with
  | nil => simp only [Path.length_nil] at hp; omega
  | @cons b c p e ih =>
    have he := kmswStage_endpoints_lt_nextVertex w n e.val e.property.1
    rw [e.property.2.2.1, e.property.2.2.2] at he
    refine ⟨?_, he.2⟩
    cases p with
    | nil => exact he.1
    | cons q f => exact (ih (by simp only [Path.length_cons]; omega)).1

/-- Helper toward Lemma 7.11; not a paper result. Every directed path in an
admissible stopped stage has length at most the source-to-sink LDP. The
extension uses proved source and sink paths; even a zero-length path with
an arbitrary stage vertex ID requires no extra allocation premise. -/
theorem ldpLower_stagePath_length_le {ell r t : ℕ} (ht : 1 ≤ t)
    (c : KMSWWalkClass ell r t)
    {a b : StagePresentVertex (codeExtend c) (t - 1)} (p : Path a b) :
    p.length ≤ ldpLengthBase (kmswWalkClassRep ht c).B := by
  classical
  by_cases hp : p.length = 0
  · rw [hp]
    exact Nat.zero_le _
  have hab := segmentPath_endpoints_allocated (codeExtend c) (t - 1) p
    (Nat.pos_of_ne_zero hp)
  let B := kmswWalkClassBase ht c
  let u : MapVertex B.map :=
    (stageVertexEquiv (codeExtend c) (t - 1)).symm ⟨a.id, hab.1⟩
  let v : MapVertex B.map :=
    (stageVertexEquiv (codeExtend c) (t - 1)).symm ⟨b.id, hab.2⟩
  have hu : stageMapVertex (codeExtend c) (t - 1) u = a := by
    change StagePresentVertex.mk
      ((stageVertexEquiv (codeExtend c) (t - 1))
        ((stageVertexEquiv (codeExtend c) (t - 1)).symm ⟨a.id, hab.1⟩)).val = a
    rw [Equiv.apply_symm_apply]
  have hv : stageMapVertex (codeExtend c) (t - 1) v = b := by
    change StagePresentVertex.mk
      ((stageVertexEquiv (codeExtend c) (t - 1))
        ((stageVertexEquiv (codeExtend c) (t - 1)).symm ⟨b.id, hab.2⟩)).val = b
    rw [Equiv.apply_symm_apply]
  obtain ⟨i, P, _⟩ := exists_simple_source_pathBase B u
  obtain ⟨j, Q, _⟩ := exists_simple_sink_pathBase B v
  obtain ⟨s, hs⟩ := (stageMap_path_iff (codeExtend c) (t - 1) i B.source u).1 ⟨P⟩
  obtain ⟨z, hz⟩ := (stageMap_path_iff (codeExtend c) (t - 1) j v B.sink).1 ⟨Q⟩
  rw [hu] at s
  rw [hv] at z
  let q := (s.comp p).comp z
  obtain ⟨R⟩ := (stageMap_path_iff (codeExtend c) (t - 1) q.length
    B.source B.sink).2 ⟨q, rfl⟩
  have hq : p.length ≤ q.length := by
    dsimp only [q]
    rw [Path.length_comp, Path.length_comp]
    omega
  have hle := hq.trans (le_ldpLengthBase B R)
  let I : BipolarBoundaryBaseIso (kmswWalkClassRep ht c).B B :=
    (B.transportIso (Fintype.equivFin _)).symm
  rw [ldpLengthBase_eq_of_baseIso I] at hle
  exact hle

private theorem segment_mapPath_length {V W : Type*} [Quiver V] [Quiver W]
    (F : Prefunctor V W) {a b : V} (p : Path a b) :
    (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- Helper toward Lemma 7.11; not a paper result. On the defining stopping
event, every path in a segment ending strictly before the hit extends inside
the stopped bipolar map to a source-to-sink path of at least that length.
The conclusion retains the actual `stoppedMap` value and uses `WithBot ℕ`.
The start time is arbitrary, so in particular it can be the first hit of
`-⌊r/2⌋`. -/
theorem ldpLower_stoppedMap_segmentPath (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) (T N : ℕ)
    (hTN : T + N < boltzmannTau r ω)
    {a b : StagePresentVertex (fun i => boltzmannKMSWStream ω (T + i)) N}
    (p : Path a b) :
    ∃ q : AllBoltzmannSpace r, stoppedMap r hr ω = some q ∧
      (p.length : WithBot ℕ) ≤ (ldpLengthBase q.2.2.out.B : WithBot ℕ) := by
  classical
  let t := boltzmannTau r ω
  let w := boltzmannKMSWStream ω
  let ell := (L w t).toNat
  let c : KMSWWalkClass ell r t :=
    ⟨stoppedWord r ω, (stoppedWord_admissible r hr ω hE).1⟩
  have ht : 1 ≤ t := (boltzmann_boundary_observable r hr ω hE).1
  have hstage : kmswStage (codeExtend c) (t - 1) = kmswStage w (t - 1) :=
    stoppedStage_eq_of_stoppedWord_eq r ω c rfl
  let F : Prefunctor (StagePresentVertex w (t - 1))
      (StagePresentVertex (codeExtend c) (t - 1)) := {
    obj := fun v => ⟨v.id⟩
    map := fun {_ _} e => by
      refine ⟨e.val, ?_, ?_, ?_, ?_⟩
      · rw [hstage]; exact e.property.1
      · rw [hstage]; exact e.property.2.1
      · rw [hstage]; exact e.property.2.2.1
      · rw [hstage]; exact e.property.2.2.2 }
  let s := (ldpLowerSegmentToStage w T N).mapPath p
  let z := (kmswStageInclusion w (T + N) (t - 1) (by dsimp [t]; omega)).mapPath s
  let P := F.mapPath z
  have hlen : P.length = p.length := by
    dsimp only [P, z, s]
    rw [segment_mapPath_length, kmswStageInclusion_length,
      ldpLowerSegmentToStage_length]
  have hbound : p.length ≤ ldpLengthBase (kmswWalkClassRep ht c).B := by
    rw [← hlen]
    exact ldpLower_stagePath_length_le ht c P
  have hmap : stoppedMap r hr ω =
      some ⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩ := by
    unfold stoppedMap stoppedIndex
    rw [dite_eq_left hE]
    dsimp only [Option.bind, stoppedWalkMapOption]
    rw [dite_eq_left ht]
    rfl
  have hmk : KMSWMapIsoClass.mk (kmswWalkClassRep ht c) =
      KMSWMapIsoClass.mk (kmswToMapIsoClass ht c).out := by
    exact (Quotient.out_eq (kmswToMapIsoClass ht c)).symm
  obtain ⟨I⟩ := (KMSWMapIsoClass.mk_eq_mk_iff _ _).mp hmk
  have heq := ldpLengthBase_eq_of_baseIso I
  refine ⟨⟨ell, ⟨t, kmswToMapIsoClass ht c⟩⟩, hmap, ?_⟩
  exact WithBot.coe_le_coe.mpr (by rw [heq]; exact hbound)

/-- Helper toward Lemma 7.11; not a paper result. The segment-to-stopped-map
bound expressed on any defined value of the existing optional map carrier.
Membership in the stopping event is derived from the map definition. -/
theorem ldpLower_segmentPath_length_le_stoppedMap (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (T N : ℕ) (hTN : T + N < boltzmannTau r ω)
    {a b : StagePresentVertex (fun i => boltzmannKMSWStream ω (T + i)) N}
    (p : Path a b) (q : AllBoltzmannSpace r)
    (hq : stoppedMap r hr ω = some q) :
    (p.length : WithBot ℕ) ≤ (ldpLengthBase q.2.2.out.B : WithBot ℕ) := by
  classical
  have hE : ω ∈ boltzmannEvent r := by
    by_contra hn
    simp only [stoppedMap, stoppedIndex, dite_eq_right hn, Option.bind_none] at hq
    cases hq
  obtain ⟨q', hq', hle⟩ := ldpLower_stoppedMap_segmentPath r hr ω hE T N hTN p
  have heq : q' = q := Option.some.inj (hq'.symm.trans hq)
  subst q'
  exact hle

/-- Helper toward Lemma 7.11; not a paper result. The deterministic inclusion
on the marked carrier used in Lemma 7.9. The mark does not change the
underlying map or its source-to-sink distance. -/
theorem ldpLower_segmentPath_length_le_stoppedMarked (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) (hE : pathCode p ∈ boltzmannEvent r) (T N : ℕ)
    (hTN : T + N < boltzmannTau r (pathCode p))
    {a b : StagePresentVertex
      (fun i => boltzmannKMSWStream (pathCode p) (T + i)) N}
    (s : Path a b) :
    (s.length : WithBot ℕ) ≤
      (ldpLengthBase (stoppedMarked r hr p).1.2.2.out.B : WithBot ℕ) := by
  obtain ⟨q, hq, hle⟩ :=
    ldpLower_stoppedMap_segmentPath r hr (pathCode p) hE T N hTN s
  have hv : (stoppedMarked r hr p).1 = q := by
    change (stoppedMap r hr (pathCode p)).getD (stoppedMarkedDefault r hr) = q
    rw [hq]
    rfl
  change (s.length : WithBot ℕ) ≤
    (fun q : AllBoltzmannSpace r => (ldpLengthBase q.2.2.out.B : WithBot ℕ))
      (stoppedMarked r hr p).1
  rw [hv]
  exact hle

/-- Helper toward Lemma 7.11; not a paper result. Specialization to the first
hit of `-⌊r/2⌋` and a path of prescribed length `m`, with the exact strict
pre-hit stopping convention of the existing stopped-stage carrier. -/
theorem ldpLower_halfHit_segment (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) (hE : pathCode p ∈ boltzmannEvent r) (N m : ℕ)
    (hTN : boltzmannTau (r / 2) (pathCode p) + N < boltzmannTau r (pathCode p))
    (hpath : ∃ a b : StagePresentVertex
      (fun i => boltzmannKMSWStream (pathCode p)
        (boltzmannTau (r / 2) (pathCode p) + i)) N,
      ∃ s : Path a b, s.length = m) :
    (m : WithBot ℕ) ≤
      (ldpLengthBase (stoppedMarked r hr p).1.2.2.out.B : WithBot ℕ) := by
  obtain ⟨a, b, s, hs⟩ := hpath
  rw [← hs]
  exact ldpLower_segmentPath_length_le_stoppedMarked r hr p hE
    (boltzmannTau (r / 2) (pathCode p)) N hTN s

/-- Helper toward Lemma 7.11; not a paper result. Decoding the centered walk
segment in `eqn-boltzmann-ldp-lower-shift` gives exactly the shifted stream
used by the deterministic inclusion, without any assumption on the path. -/
theorem ldpLower_centeredSegment_stream (p : ℕ → ℤ × ℤ) (T : ℕ) :
    boltzmannKMSWStream (pathCode (fun n => p (T + n) - p T)) =
      fun i => boltzmannKMSWStream (pathCode p) (T + i) := by
  funext i
  change pathCode (fun n => p (T + n) - p T) (i + 1) = pathCode p (T + i + 1)
  simp only [pathCode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel, sub_sub_sub_cancel_right, Nat.add_assoc]
  rw [show T + (i + 1) - 1 = T + i by omega]

/-- Helper toward Lemma 7.11; not a paper result. The inclusion stated
directly for the KMSW map of the centered walk segment appearing in the
manuscript. It applies in particular at `T = boltzmannTau (r / 2) (pathCode p)`. -/
theorem ldpLower_centeredSegment (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) (hE : pathCode p ∈ boltzmannEvent r) (T N m : ℕ)
    (hTN : T + N < boltzmannTau r (pathCode p))
    (hpath : ∃ a b : StagePresentVertex
      (boltzmannKMSWStream (pathCode (fun n => p (T + n) - p T))) N,
      ∃ s : Path a b, s.length = m) :
    (m : WithBot ℕ) ≤
      (ldpLengthBase (stoppedMarked r hr p).1.2.2.out.B : WithBot ℕ) := by
  rw [ldpLower_centeredSegment_stream] at hpath
  obtain ⟨a, b, s, hs⟩ := hpath
  rw [← hs]
  exact ldpLower_segmentPath_length_le_stoppedMarked r hr p hE T N hTN s

/-- Helper toward Lemma 7.11; not a paper result. The chance of hitting
`-⌈r/2⌉` strictly before `r²/C` is bounded uniformly in the positive integer
radius, including when the floored time horizon is zero. -/
theorem ldpLower_cell_earlyHit_probability (r : ℕ) (hr : 1 ≤ r)
    (C : ℝ) (hC : 0 < C) :
    iidCodeMeasure.real {ω | ∃ k : ℕ, (k : ℝ) < (r : ℝ) ^ 2 / C ∧
      (codeWalk ω k).2 = -(((r + 1) / 2 : ℕ) : ℤ)} ≤
      4 * Real.exp (-C / 8) := by
  let n : ℕ := ⌊(r : ℝ) ^ 2 / C⌋₊
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hround : (r : ℝ) / 2 ≤ (((r + 1) / 2 : ℕ) : ℝ) := by
    have h : r ≤ 2 * ((r + 1) / 2) := by omega
    have h' : (r : ℝ) ≤ 2 * (((r + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h
    linarith only [h']
  let E : Set (ℕ → Fin 3) := {ω | ∃ k : ℕ, (k : ℝ) < (r : ℝ) ^ 2 / C ∧
    (codeWalk ω k).2 = -(((r + 1) / 2 : ℕ) : ℤ)}
  by_cases hn : n = 0
  · have he : E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨k, hk, he⟩
      have hkn : k ≤ n := Nat.le_floor hk.le
      have hk0 : k = 0 := by omega
      rw [hk0, codeWalk_zero] at he
      have hceil : 1 ≤ (r + 1) / 2 := by omega
      dsimp only at he
      omega
    change iidCodeMeasure.real E ≤ _
    rw [he, measureReal_empty]
    positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have htail := iidCodeWalk_blockMax_tail 0 n hnpos ((r : ℝ) / 2) (by positivity)
  simp only [Nat.zero_add, codeWalk_zero, Prod.fst_sub, Prod.snd_sub,
    sub_zero] at htail
  have hsub : E ⊆ {ω | ∃ k ≤ n, (r : ℝ) / 2 ≤ |((codeWalk ω k).1 : ℝ)| ∨
      (r : ℝ) / 2 ≤ |((codeWalk ω k).2 : ℝ)|} := by
    rintro ω ⟨k, hk, he⟩
    refine ⟨k, Nat.le_floor hk.le, Or.inr ?_⟩
    rw [he]
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg]
    exact hround.trans (le_abs_self _)
  have hnc : (n : ℝ) * C ≤ (r : ℝ) ^ 2 :=
    (le_div_iff₀ hC).mp (Nat.floor_le (by positivity))
  have hexp : -((r : ℝ) / 2) ^ 2 / (2 * (n : ℝ)) ≤ -C / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith only [hnc]
  exact (measureReal_mono hsub).trans
    (htail.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)))

private theorem ldpLower_floor_scale (r : ℕ) (C : ℝ) (hC : 1 < C) :
    (r : ℝ) ^ (3 / 2 : ℝ) ≤
      2 * C * ((max 1 ⌊(r : ℝ) ^ 2 / C⌋₊ : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
  let n : ℕ := ⌊(r : ℝ) ^ 2 / C⌋₊
  have hfloor := Nat.lt_floor_add_one ((r : ℝ) ^ 2 / C)
  have hn : (1 : ℝ) ≤ ((max 1 n : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left 1 n)
  have hnm : (n : ℝ) ≤ ((max 1 n : ℕ) : ℝ) := by
    exact_mod_cast (le_max_right 1 n)
  have hsq : (r : ℝ) ^ 2 ≤ (2 * C) * ((max 1 n : ℕ) : ℝ) := by
    have hx : (r : ℝ) ^ 2 / C ≤ 2 * ((max 1 n : ℕ) : ℝ) := by
      dsimp only [n] at hnm
      linarith only [hfloor, hn, hnm]
    have h := (div_le_iff₀ (by linarith : 0 < C)).mp hx
    nlinarith only [h]
  have hp := Real.rpow_le_rpow (sq_nonneg (r : ℝ)) hsq (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hid : ((r : ℝ) ^ 2) ^ (3 / 4 : ℝ) = (r : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg r)]
    norm_num
  rw [hid, Real.mul_rpow (by positivity) (by positivity)] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_self_of_one_le (by linarith : 1 ≤ 2 * C) (by norm_num))
    (Real.rpow_nonneg (by positivity) _))

/-- Helper toward Lemma 7.11, `eqn-boltzmann-ldp-lower-cell`; not a paper
result. One pair of constants works for every positive integer radius. The
first clause says the first hit of `-⌈r/2⌉` is at least `r²/C`; it also
includes paths that never hit. The zero-stage case uses the present root
edge, so no lower cutoff on the radius is needed. -/
theorem ldpLower_cell_event (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C A : ℝ, 1 < C ∧ 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - ε ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
        (∀ k : ℕ, (k : ℝ) < (r : ℝ) ^ 2 / C →
          (codeWalk ω k).2 ≠ -(((r + 1) / 2 : ℕ) : ℤ)) ∧
        (∃ a b : StagePresentVertex (fun i => ω (i + 1)) ⌊(r : ℝ) ^ 2 / C⌋₊,
          ∃ p : Path a b, A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (p.length : ℝ))} := by
  obtain ⟨A₀, hA₀, hcell⟩ :=
    DirectedDistances.Paper.Section1.thm_cell_ldp (ε / 2) (by positivity) (by linarith)
  let C : ℝ := 64 / ε + 2
  let A : ℝ := 2 * C * A₀
  have hC : 1 < C := by
    have h : 0 < 64 / ε := by positivity
    dsimp only [C]
    linarith only [h]
  have hCpos : 0 < C := by linarith only [hC]
  have hA₀pos : 0 < A₀ := by linarith only [hA₀]
  have hA : 1 < A := by dsimp [A]; nlinarith only [hC, hA₀]
  have hApos : 0 < A := by linarith only [hA]
  refine ⟨C, A, hC, hA, ?_⟩
  intro r hr
  let n : ℕ := ⌊(r : ℝ) ^ 2 / C⌋₊
  let D : Set (ℕ → Fin 3) := {ω | ∃ a b : StagePresentVertex
    (fun i => ω (i + 1)) n, ∃ p : Path a b,
      A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ (p.length : ℝ)}
  let H : Set (ℕ → Fin 3) := {ω | ∃ k : ℕ, (k : ℝ) < (r : ℝ) ^ 2 / C ∧
    (codeWalk ω k).2 = -(((r + 1) / 2 : ℕ) : ℤ)}
  let G : Set (ℕ → Fin 3) := {ω |
    (∀ k : ℕ, (k : ℝ) < (r : ℝ) ^ 2 / C →
      (codeWalk ω k).2 ≠ -(((r + 1) / 2 : ℕ) : ℤ)) ∧ ω ∈ D}
  have hD : 1 - ε / 2 ≤ iidCodeMeasure.real D := by
    by_cases hn : n = 0
    · have hscale := ldpLower_floor_scale r C hC
      change (r : ℝ) ^ (3 / 2 : ℝ) ≤
        2 * C * ((max 1 n : ℕ) : ℝ) ^ (3 / 4 : ℝ) at hscale
      rw [hn] at hscale
      norm_num only [max_eq_left (by omega : (0 : ℕ) ≤ 1), Nat.cast_one,
        Real.one_rpow, mul_one] at hscale
      have hroot : A⁻¹ * (r : ℝ) ^ (3 / 2 : ℝ) ≤ 1 := by
        apply (inv_mul_le_iff₀ hApos).mpr
        dsimp only [A]
        nlinarith only [hscale, hC, hA₀]
      have huniv : Set.univ ⊆ D := by
        intro ω _
        refine ⟨⟨0⟩, ⟨1⟩, Hom.toPath (initialEdgeArrow (fun i => ω (i + 1)) n), ?_⟩
        simpa only [Path.length_toPath, Nat.cast_one] using hroot
      have hm := measureReal_mono (μ := iidCodeMeasure) huniv
      rw [probReal_univ] at hm
      linarith only [hm, hε]
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hscale := ldpLower_floor_scale r C hC
      change (r : ℝ) ^ (3 / 2 : ℝ) ≤
        2 * C * ((max 1 n : ℕ) : ℝ) ^ (3 / 4 : ℝ) at hscale
      rw [max_eq_right hnpos] at hscale
      refine (hcell n hnpos).trans (measureReal_mono ?_)
      intro ω hω
      obtain ⟨a, b, p, hp⟩ := hω.1
      refine ⟨a, b, p, (inv_mul_le_iff₀ hApos).mpr ?_⟩
      have hp' := (inv_mul_le_iff₀ hA₀pos).mp hp
      calc
        (r : ℝ) ^ (3 / 2 : ℝ) ≤ 2 * C * (n : ℝ) ^ (3 / 4 : ℝ) := hscale
        _ ≤ 2 * C * (A₀ * (p.length : ℝ)) :=
          mul_le_mul_of_nonneg_left hp' (by positivity)
        _ = A * (p.length : ℝ) := by dsimp only [A]; ring
  have htail : 4 * Real.exp (-C / 8) ≤ ε / 2 := by
    have hexp := Real.add_one_le_exp (C / 8)
    have hprod : (ε / 2) * (C / 8 + 1) ≥ 4 := by
      dsimp only [C]
      field_simp
      nlinarith only [hε]
    have hbound : 4 ≤ (ε / 2) * Real.exp (C / 8) :=
      hprod.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    have hdiv := (div_le_iff₀ (Real.exp_pos (C / 8))).mpr hbound
    rw [show -C / 8 = -(C / 8) by ring, Real.exp_neg]
    simpa only [div_eq_mul_inv] using hdiv
  have hH : iidCodeMeasure.real H ≤ ε / 2 :=
    (ldpLower_cell_earlyHit_probability r hr C hCpos).trans htail
  have hsub : D ⊆ G ∪ H := by
    intro ω hω
    by_cases hh : ω ∈ H
    · exact Or.inr hh
    · refine Or.inl ⟨?_, hω⟩
      intro k hk he
      exact hh ⟨k, hk, he⟩
  have hm := measureReal_mono (μ := iidCodeMeasure) hsub
  have hu := measureReal_union_le (μ := iidCodeMeasure) G H
  change 1 - ε ≤ iidCodeMeasure.real G
  linarith only [hm, hu, hD, hH]

end DirectedDistances.PaperProofs.Section7
