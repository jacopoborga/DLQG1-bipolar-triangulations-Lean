/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusDecodedSide4

/-! reader and makes no paper-completion claim. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: the boundary field is the pointwise code-only
exterior mark, with no actual-side argument. -/
theorem lMinusCodeSide4_boundary_apply (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (i : ℕ) :
    (lMinusCodeSide4 x r q hf).boundary i =
      lMinusCodeDartId r _ (lMinusCodeExteriorBoundaryDart r q i) := rfl

/-- Helper toward Lemma 5.5: the corrected marking has the same cell
carrier as decoder 2; the equivalence explicitly transports that carrier. -/
@[expose] noncomputable def lMinusCodeSide4CellEquiv (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) ≃
      GeometricSideCell (lMinusCodeSide4 x r q hf) :=
  (lMinusCodeSide2CellEquiv x r q hf).trans (Equiv.cast (by rfl))

/-- Helper toward Lemma 5.5: on encoded cells, a corrected boundary tag
is exactly equality with its intrinsic exterior dart. -/
theorem lMinusCodeSide4CellEquiv_boundary_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (i : ℕ)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    geometricSideRelation (lMinusCodeSide4 x r q hf) (.boundary i)
      (lMinusCodeSide4CellEquiv x r q hf u)
      (lMinusCodeSide4CellEquiv x r q hf v) ↔
      (match u with
       | .inl _ => False
       | .inr d => lMinusCodeExteriorBoundaryDart r q i = d) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v <;> exact (lMinusCodeDartId_injective r _).eq_iff

/-- Helper toward Lemma 5.5: the unchanged tags retain their existing
intrinsic characterization, separately from the corrected boundary tag. -/
theorem lMinusCodeSide4CellEquiv_nonboundary_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (t : TruncationRelation)
    (ht : ∀ i, t ≠ .boundary i)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    geometricSideRelation (lMinusCodeSide4 x r q hf) t
      (lMinusCodeSide4CellEquiv x r q hf u)
      (lMinusCodeSide4CellEquiv x r q hf v) ↔
      lMinusCodeRelation2 x r q hf t u v :=
  (lMinusCodeSide4_nonboundary_relation x r q hf t ht _ _).trans
    (lMinusCodeSide2CellEquiv_relation_iff x r q hf t u v)

/-- Helper toward Lemma 5.5: exterior-dart equality is preserved and
reflected by the hatted marked action. -/
theorem lMinusCodeExteriorBoundaryDart_transport_eq_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (i : ℕ)
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeExteriorBoundaryDart r q i = d ↔
      lMinusCodeExteriorBoundaryDart r q' i =
        lMinusCodeGluedDartTransportEquiv x r q q' phi d := by
  rw [← lMinusCodeExteriorBoundaryDart_transport x r q q' phi i]
  exact (lMinusCodeGluedDartTransportEquiv x r q q' phi).injective.eq_iff.symm

/-- Helper toward Lemma 5.5: the corrected boundary relation transports
on intrinsic cells, without unfolding the side realization. -/
theorem lMinusCodeSide4_boundary_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (i : ℕ)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    geometricSideRelation (lMinusCodeSide4 x r q hf) (.boundary i)
      (lMinusCodeSide4CellEquiv x r q hf u)
      (lMinusCodeSide4CellEquiv x r q hf v) ↔
    geometricSideRelation (lMinusCodeSide4 x r q' hf) (.boundary i)
      (lMinusCodeSide4CellEquiv x r q' hf
        (lMinusCodeSide2TransportEquiv x r q q' phi u))
      (lMinusCodeSide4CellEquiv x r q' hf
        (lMinusCodeSide2TransportEquiv x r q q' phi v)) := by
  rw [lMinusCodeSide4CellEquiv_boundary_iff, lMinusCodeSide4CellEquiv_boundary_iff]
  cases u with
  | inl a => rfl
  | inr d => exact lMinusCodeExteriorBoundaryDart_transport_eq_iff x r q q' phi i d



theorem lMinusCodeSide4CellEquiv_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (t : TruncationRelation)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    geometricSideRelation (lMinusCodeSide4 x r q hf) t
      (lMinusCodeSide4CellEquiv x r q hf u)
      (lMinusCodeSide4CellEquiv x r q hf v) ↔
    geometricSideRelation (lMinusCodeSide4 x r q' hf) t
      (lMinusCodeSide4CellEquiv x r q' hf
        (lMinusCodeSide2TransportEquiv x r q q' phi u))
      (lMinusCodeSide4CellEquiv x r q' hf
        (lMinusCodeSide2TransportEquiv x r q q' phi v)) := by
  by_cases hb : ∃ i, t = .boundary i
  · obtain ⟨i, rfl⟩ := hb
    exact lMinusCodeSide4_boundary_transport_iff x r q q' phi hf i u v
  · have ht : ∀ i, t ≠ .boundary i := fun i hi => hb ⟨i, hi⟩
    exact (lMinusCodeSide4CellEquiv_nonboundary_iff x r q hf t ht u v).trans
      ((lMinusCodeRelation2_transport_iff x r q q' phi hf t u v).trans
        (lMinusCodeSide4CellEquiv_nonboundary_iff x r q' hf t ht _ _).symm)

/-- Helper toward Lemma 5.5: corrected code sides are marked-isomorphic
under the hatted marked action, including the exterior boundary. -/
theorem lMinusCodeSide4_markedIso (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1) :
    Nonempty (GeometricSideMarkedIso (lMinusCodeSide4 x r q hf)
      (lMinusCodeSide4 x r q' hf)) := by
  let E := lMinusCodeSide4CellEquiv x r q hf
  let E' := lMinusCodeSide4CellEquiv x r q' hf
  let T := lMinusCodeSide2TransportEquiv x r q q' phi
  refine ⟨{ equiv := E.symm.trans (T.trans E'), relation_iff := ?_ }⟩
  intro t u v
  have hh := lMinusCodeSide4CellEquiv_transport_iff x r q q' phi hf t
    (E.symm u) (E.symm v)
  change geometricSideRelation (lMinusCodeSide4 x r q hf) t
    (E (E.symm u)) (E (E.symm v)) ↔
    geometricSideRelation (lMinusCodeSide4 x r q' hf) t
      (E' (T (E.symm u))) (E' (T (E.symm v))) at hh
  rw [E.apply_symm_apply u, E.apply_symm_apply v] at hh
  exact hh

/-- Helper toward Lemma 5.5: equal codes determine the corrected marked
class independently of the source-valid preimage. -/
theorem lMinusDecodedSide4_markedIso_of_code_eq
    {x : XDP} (q q' : LMinusPreimage x)
    (hc : lMinusCodeOf q = lMinusCodeOf q') :
    Nonempty (GeometricSideMarkedIso
      (lMinusDecodedSide4 (W := q.W) (h := q.h) (k := q.k)
        (longest := q.longest) q.hτ q.hqMode q.hfin)
      (lMinusDecodedSide4 (W := q'.W) (h := q'.h) (k := q'.k)
        (longest := q'.longest) q'.hτ q'.hqMode q'.hfin)) := by
  let phi := (lMinusPreimage_hatted_markedIso_of_code_eq q q' hc).some
  rcases q with ⟨W, h, H, hLL, longest, hmode, k, hk, hp, hτ, hqMode,
    hfin, P, Tpath, hleft⟩
  cases hmode
  rcases q' with ⟨W', h', H', hLL', longest', hmode', k', hk', hp', hτ',
    hqMode', hfin', P', Tpath', hleft'⟩
  have hlong : longest = longest' := by
    cases longest <;> cases longest'
    · rfl
    · simp at hmode'
    · simp at hmode'
    · rfl
  cases hlong
  change leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W =
    leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k' W' at hc
  let r := decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
    (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)
  let r' := decodeLMinus (if longest then XDP.ldp else XDP.sdp) k'
    (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k' W')
  let Q : Coherent (if longest then XDP.ldp else XDP.sdp) := ⟨
    boundaryFutureHattedPath k W, hqMode⟩
  let Q' : Coherent (if longest then XDP.ldp else XDP.sdp) := ⟨
    boundaryFutureHattedPath k' W', hqMode'⟩
  let hf : KMSWFiniteIncidence r.code.1 :=
    lMinus_primed_observation_finiteIncidence hτ hfin
  let hf' : KMSWFiniteIncidence r'.code.1 :=
    lMinus_primed_observation_finiteIncidence hτ' hfin'
  have hcode := lMinusCodeSide4_markedIso (if longest then XDP.ldp else XDP.sdp)
    r Q Q' phi hf
  have hq : lMinusDecodedSide4 hτ hqMode hfin =
      lMinusCodeSide4 (if longest then XDP.ldp else XDP.sdp) r Q hf := by
    rw [lMinusDecodedSide4_eq_codeSide4]
  have hq' : lMinusDecodedSide4 hτ' hqMode' hfin' =
      lMinusCodeSide4 (if longest then XDP.ldp else XDP.sdp) r' Q' hf' := by
    rw [lMinusDecodedSide4_eq_codeSide4]
  rw [hq, hq']
  simpa [r, r', decodeLMinus, hc.symm] using hcode

/-- Helper toward Lemma 5.5: choose a corrected class only on codes with
a source-valid preimage. The input contains only the two code blocks. -/
@[expose] noncomputable def LMinusSidePresentation.classOption4
    {x : XDP} (r : LMinusSidePresentation x) : Option GeometricSideClass :=
  if hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code then
    some (geometricSideClass
      (lMinusDecodedSide4 (W := hq.choose.W) (h := hq.choose.h)
        (k := hq.choose.k) (longest := hq.choose.longest)
        hq.choose.hτ hq.choose.hqMode hq.choose.hfin))
  else none

/-- Helper toward Lemma 5.5: the optional reader returns the corrected
class of every source-valid preimage, independently of its choice. -/
theorem LMinusSidePresentation.classOption4_eq_some
    {x : XDP} (r : LMinusSidePresentation x) (q : LMinusPreimage x)
    (hc : lMinusCodeOf q = r.code) :
    r.classOption4 = some (geometricSideClass
      (lMinusDecodedSide4 (W := q.W) (h := q.h) (k := q.k)
        (longest := q.longest) q.hτ q.hqMode q.hfin)) := by
  have hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code := ⟨q, hc⟩
  rw [LMinusSidePresentation.classOption4, dite_eq_left hq]
  apply congrArg some
  exact (geometricSideClass_eq_iff _ _).mpr
    (lMinusDecodedSide4_markedIso_of_code_eq hq.choose q
      (hq.choose_spec.trans hc.symm))

/-- Helper toward Lemma 5.5: absence means exactly that no source-valid
preimage of the two code blocks exists. -/
theorem LMinusSidePresentation.classOption4_eq_none_iff
    {x : XDP} (r : LMinusSidePresentation x) :
    r.classOption4 = none ↔ ¬ ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code := by
  by_cases hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code
  · rw [LMinusSidePresentation.classOption4, dite_eq_left hq]
    simp only [Option.some_ne_none, hq, not_true_eq_false]
  · rw [LMinusSidePresentation.classOption4, dite_eq_right hq]
    exact ⟨fun _ => hq, fun _ => rfl⟩

/-- Helper toward Lemma 5.5: all present values of the reader have the
same corrected class, with their complete existence characterization. -/
theorem LMinusSidePresentation.classOption4_eq_some_iff
    {x : XDP} (r : LMinusSidePresentation x) (c : GeometricSideClass) :
    r.classOption4 = some c ↔
      ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code ∧
        geometricSideClass
          (lMinusDecodedSide4 (W := q.W) (h := q.h) (k := q.k)
            (longest := q.longest) q.hτ q.hqMode q.hfin) = c := by
  constructor
  · intro hc
    have hq : ∃ q : LMinusPreimage x, lMinusCodeOf q = r.code := by
      by_contra hn
      have he := r.classOption4_eq_none_iff.mpr hn
      rw [hc] at he
      exact Option.some_ne_none c he
    refine ⟨hq.choose, hq.choose_spec, ?_⟩
    exact Option.some.inj ((r.classOption4_eq_some hq.choose hq.choose_spec).symm.trans hc)
  · rintro ⟨q, hq, rfl⟩
    exact r.classOption4_eq_some q hq

/-- Helper toward Lemma 5.5: a source-valid observation returns the class
of its actual left side, using the proved decoder-4 identification. -/
theorem LMinusPreimage.classOption4_eq_actual {x : XDP} (q : LMinusPreimage x) :
    (decodeLMinus x q.k (lMinusCodeOf q)).classOption4 =
      some (geometricSideClass (m0GeodesicSide q.hp q.P .left)) := by
  rw [LMinusSidePresentation.classOption4_eq_some (decodeLMinus x q.k (lMinusCodeOf q)) q rfl]
  rw [lMinusDecodedSide4_class_eq_actual q.hτ q.hp q.P q.hqMode
    q.Tpath q.hfin q.hleft q.hk]

open MeasureTheory Filter

/-- Helper toward Lemma 5.5: on one common probability-one event, the
actual left-side classes are the corrected decoded classes at every
nonpositive index, retaining both modes, uniqueness and pairwise coalescence. -/
theorem ae_boundaryGluing_nonpos_left_class_eq_lMinusDecodedSide4 :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (j - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n)) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        (∀ k k' : ℤ, ∃ i j : ℕ, ∀ n : ℕ,
          wholePlaneEdgeι W 0 ((P k).codePath.edge (i + n)) =
            wholePlaneEdgeι W 0 ((P k').codePath.edge (j + n))) ∧
        ∀ k : ℤ, k ≤ 0 →
          ∃ (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
            (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
            (hqMode : boundaryFutureHattedPath k W ∈
              Coherent (if longest then XDP.ldp else XDP.sdp)),
            geometricSideClass (m0GeodesicSide hp (P k) .left) =
              geometricSideClass (lMinusDecodedSide4 hτ hqMode hfin) ∧
            (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
              (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)).classOption4 =
              some (geometricSideClass (m0GeodesicSide hp (P k) .left)) := by
  filter_upwards [Xdp.m0Cut_ae_leftmost_xdp_and_pairwise_coalescence,
    wholePlane_ae_boundaryGluing_inputs] with W hgeo hglue
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hgeo
  refine ⟨H, h, hLL, hp, ?_⟩
  intro longest
  obtain ⟨R, T, P, hR, hleft, huniq, hcoal⟩ := hpaths longest
  refine ⟨R, T, P, hR, hleft, huniq, hcoal, ?_⟩
  intro k hk
  obtain ⟨hτ, hfin, _, hcoherent⟩ := hglue h k
  let hq := hcoherent (if longest then XDP.ldp else XDP.sdp)
  refine ⟨hτ, hfin, hq, ?_, ?_⟩
  · exact (lMinusDecodedSide4_class_eq_actual
      hτ hp (P k) hq (T k) hfin (hleft k) hk).symm
  · let q : LMinusPreimage (if longest then XDP.ldp else XDP.sdp) :=
      ⟨W, h, H, hLL, longest, rfl, k, hk, hp, hτ, hq, hfin, P k, T k, hleft k⟩
    exact q.classOption4_eq_actual

/-- Helper toward Lemma 5.5: selecting each lower-left record is measurable
by countable record-count threshold events. -/
private theorem measurable_lMinusExteriorRecordSelect (i : ℕ) :
    Measurable (fun p : ℕ → Fin 3 =>
      natSelect (fun m => 0 < m ∧ ∀ j < m, L p m < L p j) i) := by
  let P : (ℕ → Fin 3) → ℕ → Prop :=
    fun p m => 0 < m ∧ ∀ j < m, L p m < L p j
  have hP (m : ℕ) : MeasurableSet {p | P p m} := by
    exact measurableSet_of_factors_prefix m _ (by
      intro p p' h
      have hl (j : ℕ) (hj : j ≤ m) : L p j = L p' j :=
        L_congr (fun k hk => h k (by omega))
      unfold P
      constructor <;> rintro ⟨hm, hp⟩ <;> refine ⟨hm, ?_⟩
      · intro j hj
        rw [← hl m le_rfl, ← hl j (by omega)]
        exact hp j hj
      · intro j hj
        rw [hl m le_rfl, hl j (by omega)]
        exact hp j hj)
  have hcount (n : ℕ) : Measurable (fun p => Nat.count (P p) n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      simp only [Nat.count_succ]
      exact ih.add (measurable_const.ite (hP n) measurable_const)
  have hthreshold (m : ℕ) : MeasurableSet {p | i < Nat.count (P p) (m + 1)} :=
    (hcount (m + 1)) (Set.to_countable {n : ℕ | i < n}).measurableSet
  have hE : MeasurableSet {p | ∃ m, i < Nat.count (P p) (m + 1)} := by
    simpa only [Set.iUnion_ofPred] using MeasurableSet.iUnion hthreshold
  have hfind : Measurable
      (fun p : {p : (ℕ → Fin 3) | ∃ m, i < Nat.count (P p) (m + 1)} =>
        Nat.find p.2) :=
    measurable_find (fun p => p.2) (fun m => (hthreshold m).preimage measurable_subtype_coe)
  convert hfind.dite measurable_const hE using 1
  funext p
  simp only [natSelect, P]
  congr 2

/-- Helper toward Lemma 5.5: each retained primed exterior edge label is
a measurable function of the primed code alone. -/
theorem measurable_lMinusCodeExteriorBoundaryEdge_apply (i : ℕ) :
    Measurable (fun p : ℕ → Fin 3 => lMinusCodeExteriorBoundaryEdge p i) := by
  cases i with
  | zero => exact measurable_const
  | succ i =>
    have hcreated (m : ℕ) : Measurable (fun p : ℕ → Fin 3 => kmswLLCreatedEdge p m) := by
      refine measurable_of_factors_prefix m _ ?_
      intro p p' h
      unfold kmswLLCreatedEdge
      rw [kmswStage_congr h]
    have hpair : Measurable (fun z : ℕ × (ℕ → Fin 3) => kmswLLCreatedEdge z.2 z.1) :=
      measurable_from_prod_countable_right hcreated
    exact hpair.comp ((measurable_lMinusExteriorRecordSelect i).prodMk measurable_id)

/-- Helper toward Lemma 5.5: the whole exterior enumeration is measurable
for the countable product sigma algebra on primed edge labels. -/
theorem measurable_lMinusCodeExteriorBoundaryEdge :
    Measurable lMinusCodeExteriorBoundaryEdge :=
  measurable_pi_iff.mpr measurable_lMinusCodeExteriorBoundaryEdge_apply

/-- Helper toward Lemma 5.5: the measurable exterior enumeration can be
read directly from the first block of a presentation. -/
theorem measurable_lMinusCodeExteriorBoundaryEdge_presentation (x : XDP) :
    Measurable (fun r : LMinusSidePresentation x =>
      lMinusCodeExteriorBoundaryEdge r.code.1) :=
  measurable_lMinusCodeExteriorBoundaryEdge.comp
    (measurable_lMinusSidePresentation_code x).fst

/-- Helper toward Lemma 5.5: every observed nonpositive left presentation
has a present corrected class almost surely, for either XDP mode. -/
theorem ae_decodeLMinus_leftSideObsNonpos_classOption4_isSome
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ((decodeLMinus x k (leftSideObsNonpos x k W)).classOption4).isSome = true := by
  filter_upwards [ae_boundaryGluing_nonpos_left_class_eq_lMinusDecodedSide4] with W hW
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hW
  cases x with
  | ldp =>
    obtain ⟨R, T, P, _, _, _, _, hclass⟩ := hpaths true
    obtain ⟨hτ, hfin, hq, _, hr⟩ := hclass k hk
    exact congrArg Option.isSome hr
  | sdp =>
    obtain ⟨R, T, P, _, _, _, _, hclass⟩ := hpaths false
    obtain ⟨hτ, hfin, hq, _, hr⟩ := hclass k hk
    exact congrArg Option.isSome hr

/-- Helper toward Lemma 5.5: the observed presence indicator is a.e.
measurable; this does not assert measurability of the class-valued reader. -/
theorem aemeasurable_decodeLMinus_leftSideObsNonpos_classOption4_isSome
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable
      (fun W => ((decodeLMinus x k (leftSideObsNonpos x k W)).classOption4).isSome)
      wholePlaneIIDCodeMeasure :=
  ⟨fun _ => true, measurable_const,
    ae_decodeLMinus_leftSideObsNonpos_classOption4_isSome x k hk⟩

































end DirectedDistances.PaperProofs.Section5

