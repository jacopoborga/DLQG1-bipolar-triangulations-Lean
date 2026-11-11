module

public import DirectedDistances.Recursive.BusemannRightSideLocalizationSdp
public import DirectedDistances.Recursive.BusemannRightSideLocality
public import DirectedDistances.Recursive.ThinCodeDistanceDecoders
import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfSeamArg

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.

The SDP finite-target truncation-difference determination, truncation formula, and
right-code locality are proved here. The finite decoder uses coherent geometric
realizations, so representative invariance is not consumed. Both eventual values
remain nested, with fixed-target decoding valid beyond that target. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "D" =>
  selectedCutCoherentDomain XDP.sdp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HL" q => sourceAncestor_left_nonneg
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HT" q => sourceAncestor_left_transient
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HR" q => sourceAncestor_right_unbounded
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "P" q => sourceAncestorPath
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "RB" => fun (q : D) (j : ℕ) =>
  thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.right j
local notation "BD" => fun (q : D) (j : ℕ) =>
  thinMapBoundaryDart (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.right j
local notation "AV" => fun (q : D) (s : ℕ) =>
  sourceAncestorVertices (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.right s
local notation "AE" => fun (q : D) (s : ℕ) =>
  sourceAncestorEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.right s
local notation "AD" => fun (q : D) (s : ℕ) =>
  sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q) ThinMapSide.right s
local notation "AR" => fun (q : D) (s : ℕ) =>
  geometricAncestorRelation XDP.sdp renewalTime renewalTime_positiveSuccessTime
    ThinMapSide.right s q
local notation "Iso" => fun (q q' : D) (s : ℕ) =>
  GeometricAncestorMarkedIso XDP.sdp renewalTime renewalTime_positiveSuccessTime
    ThinMapSide.right s q q'
local notation "TC" =>
  thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime ThinMapSide.right

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Equal right finite codes determine the difference of the attained SDP minima for -/
@[expose] def RightTruncationSdpDifferenceDetermination : Prop :=
  ∀ (q q' : D) (j m s : ℕ), j ≤ m → m ≤ s → TC q.1 s = TC q'.1 s →
    ((sInf (rightSideSdpLengths q j m) : ℕ) : ℤ) -
        ((sInf (rightSideSdpLengths q 0 m) : ℕ) : ℤ) =
      ((sInf (rightSideSdpLengths q' j m) : ℕ) : ℤ) -
        ((sInf (rightSideSdpLengths q' 0 m) : ℕ) : ℤ)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A measurable finite-code decoder followed by an eventual value in the truncation index
recovers each sufficiently late finite-target SDP difference. Source: -/
@[expose] def RightTruncationSdpFormula : Prop :=
  ∃ d : ℕ → ℕ → ℕ → Option FiniteThinMap → ℤ,
    (∀ j m s, Measurable (d j m s)) ∧
    ∀ᵐ ω ∂iidCodeMeasure, ∀ j : ℕ, ∀ᶠ m in atTop,
      boundarySdpDifference ω (j : ℤ) m =
        eventualIntValue 0 (fun s => d j m s
          (thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime .right
            (integrateCodes (hatLawCodes ω)) s))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The directed edge step encoded by the marked ancestor relation. -/
private def markedStep {α : Type*} (r : TruncationRelation → α → α → Prop)
    (u v : α) : Prop :=
  ∃ d b, r .oriented d d ∧ r .opposite d b ∧ r .incident d u ∧ r .incident b v

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A finite walk whose steps use that marked relation. -/
private def markedWalk {α : Type*} (r : TruncationRelation → α → α → Prop) :
    ℕ → α → α → Prop
  | 0, u, v => u = v
  | n + 1, u, v => ∃ z, markedWalk r n u z ∧ markedStep r z v

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Marked walks transfer across relation-preserving equivalences. -/
private theorem markedWalk_map {α β : Type*}
    (r : TruncationRelation → α → α → Prop)
    (r' : TruncationRelation → β → β → Prop) (e : α ≃ β)
    (he : ∀ t x y, r t x y ↔ r' t (e x) (e y))
    (n : ℕ) (u v : α) (h : markedWalk r n u v) :
    markedWalk r' n (e u) (e v) := by
  induction n generalizing v with
  | zero => exact congrArg e h
  | succ n ih =>
    obtain ⟨z, hz, d, b, hd, hb, hu, hv⟩ := h
    exact ⟨e z, ih z hz, e d, e b, (he _ _ _).mp hd,
      (he _ _ _).mp hb, (he _ _ _).mp hu, (he _ _ _).mp hv⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked isomorphism maps ancestor vertices to ancestor vertices. -/
private theorem iso_vertex {q q' : D} {s : ℕ} (I : Iso q q' s) (v : AV q s) :
    ∃ z : AV q' s, I.equiv (.inl v) = .inl z := by
  have h := (I.relation_iff .vertex (.inl v) (.inl v)).mp (show True from trivial)
  cases he : I.equiv (.inl v) with
  | inl z => exact ⟨z, rfl⟩
  | inr d => rw [he] at h; exact False.elim h

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked isomorphism maps ancestor darts to ancestor darts. -/
private theorem iso_dart {q q' : D} {s : ℕ} (I : Iso q q' s) (d : AD q s) :
    ∃ z : AD q' s, I.equiv (.inr d) = .inr z := by
  cases he : I.equiv (.inr d) with
  | inr z => exact ⟨z, rfl⟩
  | inl v =>
    have h := (I.relation_iff .vertex (.inr d) (.inr d)).mpr
      (by rw [he]; trivial)
    exact False.elim h

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Marked directed steps are exactly present right-side edges. -/
private theorem step_iff (q : D) (s : ℕ) (u v : AV q s) :
    markedStep (AR q s) (.inl u) (.inl v) ↔
      ∃ e ∈ AE q s, EdgePresent (W q) e ∧
        edgeWest (W q) e = u.1 ∧ edgeEast (W q) e = v.1 := by
  constructor
  · rintro ⟨d, b, hd, hb, hu, hv⟩
    cases d with
    | inl d => exact False.elim hd
    | inr d =>
      cases b with
      | inl b => exact False.elim hb
      | inr b =>
        change (EdgePresent (W q) d.1.1 ∧ d.1.2 = false) at hd
        change (d.1.1, !d.1.2) = b.1 at hb
        change (if d.1.2 then edgeEast (W q) d.1.1 else edgeWest (W q) d.1.1) = _ at hu
        change (if b.1.2 then edgeEast (W q) b.1.1 else edgeWest (W q) b.1.1) = _ at hv
        rw [← hb, hd.2] at hv
        rw [hd.2] at hu
        exact ⟨d.1.1, d.2, hd.1, hu, hv⟩
  · rintro ⟨e, he, hp, hu, hv⟩
    exact ⟨.inr ⟨(e, false), he⟩, .inr ⟨(e, true), he⟩,
      ⟨hp, rfl⟩, rfl, hu, hv⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An ancestor-restricted path gives a marked walk of equal length. -/
private theorem walk_of_path (q : D) (s : ℕ) {u v : PresentVertex (W q)}
    (p : Path u v) (hu : u.id ∈ AV q s) (hv : v.id ∈ AV q s)
    (hp : ∀ e ∈ pathEdgeList p, e ∈ AE q s) :
    markedWalk (AR q s) p.length (.inl ⟨u.id, hu⟩) (.inl ⟨v.id, hv⟩) := by
  induction p with
  | nil => rfl
  | @cons y z p e ih =>
    have he : e.val ∈ AE q s := hp e.val
      (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
    have hy : y.id ∈ AV q s := e.property.2.1 ▸ he.2.1
    refine ⟨.inl ⟨y.id, hy⟩, ih hy (fun f hf =>
      hp f (List.mem_append.mpr (Or.inl hf))), ?_⟩
    exact (step_iff q s _ _).mpr ⟨e.val, he, e.property⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked walk reconstructs an ancestor-restricted path. -/
private theorem path_of_walk (q : D) (s n : ℕ) (u v : AV q s)
    (h : markedWalk (AR q s) n (.inl u) (.inl v)) :
    ∃ p : Path (⟨u.1⟩ : PresentVertex (W q)) ⟨v.1⟩,
      p.length = n ∧ ∀ e ∈ pathEdgeList p, e ∈ AE q s := by
  induction n generalizing v with
  | zero =>
    have huv : u = v := Sum.inl.inj h
    subst v
    exact ⟨.nil, rfl, fun e he => False.elim (List.not_mem_nil he)⟩
  | succ n ih =>
    obtain ⟨z, hz, hs⟩ := h
    cases z with
    | inr d =>
      obtain ⟨a, b, _, _, ha, _⟩ := hs
      cases a <;> exact False.elim ha
    | inl z =>
      obtain ⟨p, hp, hpe⟩ := ih z hz
      obtain ⟨e, he, hpres, hw, hh⟩ := (step_iff q s z v).mp hs
      let f : (⟨z.1⟩ : PresentVertex (W q)) ⟶ ⟨v.1⟩ := ⟨e, hpres, hw, hh⟩
      refine ⟨p.cons f, by rw [Path.length_cons, hp], ?_⟩
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hpe d hd
      · exact List.mem_singleton.mp hd ▸ he

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Ordered right boundary vertices lie in later ancestor restrictions. -/
private theorem boundary_mem (q : D) (i s : ℕ) (hi : i ≤ s) : RB q i ∈ AV q s :=
  (ancestorPos_boundary_vertex_mem_iff (W q) (HF q) (HL q) (HT q) (HR q)
    (P q) .right i s).mpr hi

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Marked isomorphisms preserve each indexed right boundary vertex. -/
private theorem iso_boundary {q q' : D} {s : ℕ} (I : Iso q q' s)
    (i : ℕ) (hi : i ≤ s) :
    I.equiv (.inl ⟨RB q i, boundary_mem q i s hi⟩) =
      .inl ⟨RB q' i, boundary_mem q' i s hi⟩ := by
  obtain ⟨z, hz⟩ := iso_vertex I ⟨RB q i, boundary_mem q i s hi⟩
  rw [hz]
  apply congrArg Sum.inl
  apply Subtype.ext
  cases i with
  | zero =>
    have h := (I.relation_iff .root _ _).mp
      (show AR q s .root (.inl ⟨RB q 0, boundary_mem q 0 s hi⟩)
        (.inl ⟨RB q 0, boundary_mem q 0 s hi⟩) from rfl)
    rw [hz] at h
    exact h
  | succ i =>
    have hd : BD q i ∈ AD q s :=
      (ancestorPos_boundary_dart_mem_iff (W q) (HF q) (HL q) (HT q) (HR q)
        (P q) .right i s).mpr (by omega)
    let d : AD q s := ⟨BD q i, hd⟩
    let b : AD q s := ⟨((BD q i).1, true), hd⟩
    obtain ⟨d', hd'⟩ := iso_dart I d
    obtain ⟨b', hb'⟩ := iso_dart I b
    have hbd := (I.relation_iff (.boundary i) (.inr d) (.inr d)).mp rfl
    rw [hd'] at hbd
    change BD q' i = d'.1 at hbd
    have hop := (I.relation_iff .opposite (.inr d) (.inr b)).mp rfl
    rw [hd', hb'] at hop
    change (d'.1.1, !d'.1.2) = b'.1 at hop
    have hin := (I.relation_iff .incident (.inr b)
      (.inl ⟨RB q (i + 1), boundary_mem q (i + 1) s hi⟩)).mp rfl
    rw [hb', hz] at hin
    change (if b'.1.2 then edgeEast (W q') b'.1.1 else edgeWest (W q') b'.1.1) = z.1
      at hin
    rw [← hop, ← hbd] at hin
    exact hin.symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked isomorphism preserves attainable boundary path lengths. -/
private theorem lengths_subset_of_iso {q q' : D} {s : ℕ} (I : Iso q q' s)
    (j m : ℕ) (hms : m ≤ s) (hjs : j ≤ s) :
    rightSideSdpLengths q j m ⊆ rightSideSdpLengths q' j m := by
  intro n hn
  rw [rightSideSdpLengths_eq_ancestorLengths q j m s hms] at hn
  obtain ⟨p, hp, he⟩ := hn
  have hwalk := walk_of_path q s p (boundary_mem q j s hjs) (boundary_mem q m s hms) he
  have hmap := markedWalk_map (AR q s) (AR q' s) I.equiv I.relation_iff
    p.length _ _ hwalk
  rw [iso_boundary I j hjs, iso_boundary I m hms] at hmap
  obtain ⟨r, hr, hre⟩ := path_of_walk q' s p.length _ _ hmap
  rw [rightSideSdpLengths_eq_ancestorLengths q' j m s hms]
  exact ⟨r, hr.trans hp, hre⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Equal finite right codes preserve each attainable length between ordered boundary endpoints. -/
private theorem rightSideSdpLengths_eq_of_truncation (q q' : D) (j m s : ℕ)
    (hjm : j ≤ m) (hms : m ≤ s) (hc : TC q.1 s = TC q'.1 s) :
    rightSideSdpLengths q j m = rightSideSdpLengths q' j m := by
  have hclass : selectedCutAncestorClass XDP.sdp renewalTime
      renewalTime_positiveSuccessTime .right s q =
      selectedCutAncestorClass XDP.sdp renewalTime
        renewalTime_positiveSuccessTime .right s q' := by
    rw [thinSideCode_coe, thinSideCode_coe] at hc
    dsimp only at hc
    rw [thinTruncationAt_eq_some_selectedCutAncestorClass,
      thinTruncationAt_eq_some_selectedCutAncestorClass] at hc
    exact Option.some.inj hc
  obtain ⟨I⟩ := (selectedCutAncestorClass_eq_iff_geometric_iso XDP.sdp renewalTime
    renewalTime_positiveSuccessTime (sourceAncestorCutRealization_renewal .sdp)
    .right s q q').mp hclass
  let J : Iso q' q s := ⟨I.equiv.symm, fun t x y => by
    simpa only [Equiv.apply_symm_apply] using
      (I.relation_iff t (I.equiv.symm x) (I.equiv.symm y)).symm⟩
  exact Set.Subset.antisymm (lengths_subset_of_iso I j m hms (hjm.trans hms))
    (lengths_subset_of_iso J j m hms (hjm.trans hms))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite marked-code determination of both attained minima and their integer difference. -/
theorem rightTruncationSdpDifferenceDetermination_proved :
    RightTruncationSdpDifferenceDetermination := by
  intro q q' j m s hjm hms hc
  rw [rightSideSdpLengths_eq_of_truncation q q' j m s hjm hms hc,
    rightSideSdpLengths_eq_of_truncation q q' 0 m s (Nat.zero_le m) hms hc]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A finite-code decoder obtained from any coherent realization of that code. Outside the
realized code range it returns zero, which is not an unreachable-distance convention. -/
private noncomputable def rightTruncationSdpDecoder
    (j m s : ℕ) (c : Option FiniteThinMap) : ℤ := by
  classical
  exact if h : ∃ q : D, TC q.1 s = c then
    ((sInf (rightSideSdpLengths h.choose j m) : ℕ) : ℤ) -
      ((sInf (rightSideSdpLengths h.choose 0 m) : ℕ) : ℤ)
  else 0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The decoder recovers the actual finite-target difference at every sufficiently large
truncation level, uniformly over all coherent realizations of that finite code. -/
private theorem rightTruncationSdpDecoder_eq (q : D) (j m s : ℕ)
    (hjm : j ≤ m) (hms : m ≤ s) :
    rightTruncationSdpDecoder j m s (TC q.1 s) =
      ((sInf (rightSideSdpLengths q j m) : ℕ) : ℤ) -
        ((sInf (rightSideSdpLengths q 0 m) : ℕ) : ℤ) := by
  classical
  have h : ∃ q' : D, TC q'.1 s = TC q.1 s := ⟨q, rfl⟩
  rw [rightTruncationSdpDecoder, dite_eq_left h]
  exact rightTruncationSdpDifferenceDetermination_proved h.choose q j m s hjm hms
    h.choose_spec

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Almost surely, each target's boundary difference eventually equals its decoder's eventual value. -/
private theorem rightTruncationSdpDecoder_formula :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ j : ℕ, ∀ᶠ m in atTop,
      boundarySdpDifference ω (j : ℤ) m = eventualIntValue 0
        (fun s => rightTruncationSdpDecoder j m s
          (TC (integrateCodes (hatLawCodes ω)) s)) := by
  filter_upwards [rightClosedSideSdpLocalization_proved] with ω hω
  obtain ⟨h, q, hq, _, _, hloc⟩ := hω
  intro j
  filter_upwards [hloc j, eventually_ge_atTop j] with m hm hjm
  obtain ⟨nj, n0, hsj, hs0, _, _, hd⟩ := hm
  rw [← hq]
  symm
  apply eventualIntValue_eq
  filter_upwards [eventually_ge_atTop m] with s hms
  rw [rightTruncationSdpDecoder_eq q j m s hjm hms, hsj.csInf_eq, hs0.csInf_eq]
  exact hd.symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The discrete finite-code decoder gives the eventual truncation formula for every -/
theorem rightTruncationSdpFormula_proved : RightTruncationSdpFormula :=
  ⟨rightTruncationSdpDecoder, fun _ _ _ => measurable_from_top,
    rightTruncationSdpDecoder_formula⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Tail-equal integer sequences have equal total eventual values. -/
private theorem eventualIntValue_congr_tail {u v : ℕ → ℤ} (h : u =ᶠ[atTop] v) :
    eventualIntValue 0 u = eventualIntValue 0 v := by
  classical
  by_cases hu : ∃ z : ℤ, ∀ᶠ n in atTop, u n = z
  · obtain ⟨z, hz⟩ := hu
    have hv : ∀ᶠ n in atTop, v n = z := by
      filter_upwards [h, hz] with n hn hzn
      exact hn.symm.trans hzn
    exact (eventualIntValue_eq 0 hz).trans (eventualIntValue_eq 0 hv).symm
  · have hv : ¬ ∃ z : ℤ, ∀ᶠ n in atTop, v n = z := by
      rintro ⟨z, hz⟩
      apply hu
      refine ⟨z, ?_⟩
      filter_upwards [h, hz] with n hn hzn
      exact hn.trans hzn
    rw [eventualIntValue_eq_default 0 hu, eventualIntValue_eq_default 0 hv]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The right-code Busemann decoder retains both eventual values. Fixed-target decoding
therefore needs no interchange of limits or convergence along a diagonal of targets. -/
private noncomputable def rightBusemannSdpDecoder
    (c : ℕ → Option FiniteThinMap) (j : ℕ) : ℤ :=
  eventualIntValue 0 (fun m => eventualIntValue 0
    (fun s => rightTruncationSdpDecoder j m s (c s)))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The iterated eventual-value decoder is measurable for the product code sigma algebra. -/
private theorem measurable_rightBusemannSdpDecoder : Measurable rightBusemannSdpDecoder := by
  apply Measurable.of_eval
  intro j
  apply measurable_eventualIntValue 0
  intro m
  apply measurable_eventualIntValue 0
  intro s
  exact (show Measurable (rightTruncationSdpDecoder j m s) from
    measurable_from_top).comp (measurable_pi_apply s)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The right finite marked code measurably determines the nonnegative SDP Busemann profile.
This uses fixed boundary targets inside larger ancestor restrictions, not their targets. -/
theorem rightBusemannSdpLocality_proved : RightBusemannSdpLocality := by
  refine ⟨rightBusemannSdpDecoder, measurable_rightBusemannSdpDecoder, ?_⟩
  filter_upwards [rightTruncationSdpDecoder_formula] with ω hω
  funext j
  exact eventualIntValue_congr_tail (hω j)

end DirectedDistances.Recursive
