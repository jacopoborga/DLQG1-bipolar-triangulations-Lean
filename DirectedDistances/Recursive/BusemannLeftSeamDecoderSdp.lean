module

public import DirectedDistances.Recursive.BusemannRightSideLocalizationSdp
public import DirectedDistances.Recursive.BusemannLeftSideDecompositionSdp
public import DirectedDistances.Recursive.ThinCodeDistanceDecoders
public import DirectedDistances.Recursive.ThinCodeDistanceDecoders
import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfSeamArg

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.

The left finite-code decoder reads paths from the marked outer boundary to the marked
seam inside finite ancestor restrictions. Marked-isomorphism invariance and product
measurability are proved. Its identification with raw paths in the H-image of the
hatted closed left side remains an explicit open proposition. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "ThinCode" => (ℕ → Option FiniteThinMap)
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
local notation "LB" => fun (q : D) (j : ℕ) =>
  thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.left j
local notation "BD" => fun (q : D) (j : ℕ) =>
  thinMapBoundaryDart (W q) (HF q) (HL q) (HT q) (HR q) ThinMapSide.left j
local notation "AV" => fun (q : D) (s : ℕ) =>
  sourceAncestorVertices (W q) (HF q) (HL q) (HT q) (HR q) (P q)
    ThinMapSide.left s
local notation "AE" => fun (q : D) (s : ℕ) =>
  sourceAncestorEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q)
    ThinMapSide.left s
local notation "AD" => fun (q : D) (s : ℕ) =>
  sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q)
    ThinMapSide.left s
local notation "AR" => fun (q : D) (s : ℕ) =>
  geometricAncestorRelation XDP.sdp renewalTime renewalTime_positiveSuccessTime
    ThinMapSide.left s q
local notation "Iso" => fun (q q' : D) (s : ℕ) =>
  GeometricAncestorMarkedIso XDP.sdp renewalTime renewalTime_positiveSuccessTime
    ThinMapSide.left s q q'
local notation "TC" =>
  thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
local notation "Tldp" =>
  thinSideCode XDP.sdp renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The directed step encoded by the finite marked ancestor relation. -/
private def markedStep {α : Type*} (r : TruncationRelation → α → α → Prop)
    (u v : α) : Prop :=
  ∃ d b, r .oriented d d ∧ r .opposite d b ∧ r .incident d u ∧ r .incident b v

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite walks encoded by marked incidence and orientation relations. -/
private def markedWalk {α : Type*} (r : TruncationRelation → α → α → Prop) :
    ℕ → α → α → Prop
  | 0, u, v => u = v
  | n + 1, u, v => ∃ z, markedWalk r n u z ∧ markedStep r z v

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Marked walks transport through relation-preserving equivalences. -/
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
Ancestor vertices and darts remain in their respective carrier under a marked isomorphism. -/
private theorem iso_vertex {q q' : D} {s : ℕ} (I : Iso q q' s)
    (v : AV q s) : ∃ z : AV q' s, I.equiv (.inl v) = .inl z := by
  have h := (I.relation_iff .vertex (.inl v) (.inl v)).mp trivial
  cases he : I.equiv (.inl v) with
  | inl z => exact ⟨z, rfl⟩
  | inr d => rw [he] at h; exact False.elim h

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Ancestor darts remain darts under a marked isomorphism. -/
private theorem iso_dart {q q' : D} {s : ℕ} (I : Iso q q' s)
    (d : AD q s) : ∃ z : AD q' s, I.equiv (.inr d) = .inr z := by
  cases he : I.equiv (.inr d) with
  | inr z => exact ⟨z, rfl⟩
  | inl v =>
    have h := (I.relation_iff .vertex (.inr d) (.inr d)).mpr (by rw [he]; trivial)
    exact False.elim h

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Marked directed steps are precisely present edges in the ancestor restriction. -/
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
A finite path in an ancestor restriction gives a marked walk of equal length. -/
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
A marked walk reconstructs an ancestor-restricted path of the same length. -/
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
      let f : (⟨z.1⟩ : PresentVertex (W q)) ⟶ ⟨v.1⟩ :=
        ⟨e, hpres, hw, hh⟩
      refine ⟨p.cons f, by rw [Path.length_cons, hp], ?_⟩
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hpe d hd
      · exact List.mem_singleton.mp hd ▸ he

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The left boundary vertex is present in its ancestor restriction exactly through its index. -/
private theorem boundary_mem (q : D) (i s : ℕ) (hi : i ≤ s) :
    LB q i ∈ AV q s :=
  (ancestorPos_boundary_vertex_mem_iff (W q) (HF q) (HL q) (HT q) (HR q)
    (P q) .left i s).mpr hi

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked isomorphism sends each indexed left boundary vertex to its counterpart. -/
private theorem iso_boundary {q q' : D} {s : ℕ} (I : Iso q q' s)
    (i : ℕ) (hi : i ≤ s) :
    I.equiv (.inl ⟨LB q i, boundary_mem q i s hi⟩) =
      .inl ⟨LB q' i, boundary_mem q' i s hi⟩ := by
  obtain ⟨z, hz⟩ := iso_vertex I ⟨LB q i, boundary_mem q i s hi⟩
  rw [hz]
  apply congrArg Sum.inl
  apply Subtype.ext
  cases i with
  | zero =>
    have h := (I.relation_iff .root _ _).mp
      (show AR q s .root (.inl ⟨LB q 0, boundary_mem q 0 s hi⟩)
        (.inl ⟨LB q 0, boundary_mem q 0 s hi⟩) from rfl)
    rw [hz] at h
    exact h
  | succ i =>
    have hd : BD q i ∈ AD q s :=
      (ancestorPos_boundary_dart_mem_iff (W q) (HF q) (HL q) (HT q) (HR q)
        (P q) .left i s).mpr (by omega)
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
      (.inl ⟨LB q (i + 1), boundary_mem q (i + 1) s hi⟩)).mp rfl
    rw [hb', hz] at hin
    change (if b'.1.2 then edgeEast (W q') b'.1.1 else edgeWest (W q') b'.1.1) = z.1
      at hin
    rw [← hop, ← hbd] at hin
    exact hin.symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The finite truncation's seam marker exists exactly when its indexed seam edge is retained. -/
private theorem seam_mem_iff (q : D) (t s : ℕ) :
    (P q).edge t ∈ AE q s ↔
      ∃ d : AD q s, AR q s (.seam t) (.inr d) (.inr d) := by
  constructor
  · intro ht
    exact ⟨⟨((P q).edge t, false), ht⟩, rfl⟩
  · rintro ⟨⟨⟨e, b⟩, he⟩, hd⟩
    change ((P q).edge t, false) = (e, b) at hd
    cases hd
    exact he

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked isomorphism preserves whether a specified seam dart is retained. -/
private theorem iso_seam_mem_iff {q q' : D} {s : ℕ} (I : Iso q q' s)
    (t : ℕ) : (P q).edge t ∈ AE q s ↔ (P q').edge t ∈ AE q' s := by
  rw [seam_mem_iff q t s, seam_mem_iff q' t s]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨d', hd'⟩ := iso_dart I d
    have hs := (I.relation_iff (.seam t) (.inr d) (.inr d)).mp hd
    rw [hd'] at hs
    exact ⟨d', hs⟩
  · rintro ⟨d', hd'⟩
    let J : Iso q' q s := ⟨I.equiv.symm, fun tag x y => by
      simpa only [Equiv.apply_symm_apply] using
        (I.relation_iff tag (I.equiv.symm x) (I.equiv.symm y)).symm⟩
    obtain ⟨d, hd⟩ := iso_dart J d'
    have hs := (J.relation_iff (.seam t) (.inr d') (.inr d')).mp hd'
    rw [hd] at hs
    exact ⟨d, hs⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked isomorphism sends each retained seam vertex to its indexed counterpart. -/
private theorem iso_seam {q q' : D} {s : ℕ} (I : Iso q q' s)
    (t : ℕ) (ht : (P q).edge t ∈ AE q s) :
    I.equiv (.inl ⟨((P q).initial t).1.id, by
      have htail := ((P q).edge_outgoing_at_initial (W q) t).2
      exact htail.symm ▸ ht.2.1⟩) =
      .inl ⟨((P q').initial t).1.id, by
        have htag := (seam_mem_iff q t s).mp ht
        obtain ⟨d, hd⟩ := htag
        obtain ⟨d', hd'⟩ := iso_dart I d
        have hs := (I.relation_iff (.seam t) (.inr d) (.inr d)).mp hd
        rw [hd'] at hs
        have ht' : (P q').edge t ∈ AE q' s :=
          (seam_mem_iff q' t s).mpr ⟨d', hs⟩
        have htail := ((P q').edge_outgoing_at_initial (W q') t).2
        exact htail.symm ▸ ht'.2.1⟩ := by
  have htail := ((P q).edge_outgoing_at_initial (W q) t).2
  have hmem : ((P q).initial t).1.id ∈ AV q s := htail.symm ▸ ht.2.1
  obtain ⟨z, hz⟩ := iso_vertex I ⟨((P q).initial t).1.id, hmem⟩
  obtain ⟨d, hd⟩ := (seam_mem_iff q t s).mp ht
  have hactual : ((P q).edge t, false) = d.1 := by
    change ((P q).edge t, false) = d.1 at hd
    exact hd
  obtain ⟨d', hd'⟩ := iso_dart I d
  have hs := (I.relation_iff (.seam t) (.inr d) (.inr d)).mp hd
  rw [hd'] at hs
  change ((P q').edge t, false) = d'.1 at hs
  rw [hz]
  apply congrArg Sum.inl
  apply Subtype.ext
  have hinc : AR q s .incident (.inr d)
      (.inl ⟨((P q).initial t).1.id, hmem⟩) := by
    change (if d.1.2 then edgeEast (W q) d.1.1 else edgeWest (W q) d.1.1) = _
    rw [← hactual]
    exact htail
  have hin := (I.relation_iff .incident (.inr d)
    (.inl ⟨((P q).initial t).1.id, hmem⟩)).mp hinc
  rw [hd', hz] at hin
  change (if d'.1.2 then edgeEast (W q') d'.1.1 else edgeWest (W q') d'.1.1) = z.1
    at hin
  rw [← hs] at hin
  change edgeWest (W q') ((P q').edge t) = z.1 at hin
  have htail' := ((P q').edge_outgoing_at_initial (W q') t).2
  exact hin.symm.trans htail'

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Attainable lengths from a left outer-boundary vertex to a seam vertex inside one finite
ancestor restriction. Missing endpoint marks give the empty set. -/
@[expose] def leftSeamSdpLengths (q : D) (i t s : ℕ) : Set ℕ :=
  {n | i ≤ s ∧ (P q).edge t ∈ AE q s ∧
    ∃ p : Path (⟨LB q i⟩ : PresentVertex (W q))
      ⟨((P q).initial t).1.id⟩,
      p.length = n ∧ ∀ e ∈ pathEdgeList p, e ∈ AE q s}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked isomorphism preserves all finite directed path lengths between the left boundary
and seam marks, including when either mark is absent. -/
private theorem leftSeamSdpLengths_eq_of_iso {q q' : D} {s i t : ℕ}
    (I : Iso q q' s) :
    leftSeamSdpLengths q i t s = leftSeamSdpLengths q' i t s := by
  classical
  ext n
  constructor
  · rintro ⟨hi, ht, p, hp, he⟩
    have hb := boundary_mem q i s hi
    have htail := ((P q).edge_outgoing_at_initial (W q) t).2
    have hwalk := walk_of_path q s p hb (htail.symm ▸ ht.2.1) he
    have hmap := markedWalk_map (AR q s) (AR q' s) I.equiv I.relation_iff
      p.length _ _ hwalk
    rw [iso_boundary I i hi, iso_seam I t ht] at hmap
    obtain ⟨r, hr, hre⟩ := path_of_walk q' s p.length _ _ hmap
    exact ⟨hi, (iso_seam_mem_iff I t).mp ht, r, hr.trans hp, hre⟩
  · rintro ⟨hi, ht, p, hp, he⟩
    have hb' := boundary_mem q' i s hi
    let J : Iso q' q s := ⟨I.equiv.symm, fun tag x y => by
      simpa only [Equiv.apply_symm_apply] using
        (I.relation_iff tag (I.equiv.symm x) (I.equiv.symm y)).symm⟩
    have htail := ((P q').edge_outgoing_at_initial (W q') t).2
    have hwalk := walk_of_path q' s p hb' (htail.symm ▸ ht.2.1) he
    have hmap := markedWalk_map (AR q' s) (AR q s) J.equiv J.relation_iff
      p.length _ _ hwalk
    rw [iso_boundary J i hi, iso_seam J t ht] at hmap
    obtain ⟨r, hr, hre⟩ := path_of_walk q s p.length _ _ hmap
    exact ⟨hi, (iso_seam_mem_iff J t).mp ht, r, hr.trans hp, hre⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Equal left finite codes preserve the SDP length sets between their marked endpoints. -/
theorem leftSeamSdpTruncationDetermination_proved (q q' : D) (i t s : ℕ)
    (hc : TC q.1 s = TC q'.1 s) :
    leftSeamSdpLengths q i t s = leftSeamSdpLengths q' i t s := by
  have hclass : selectedCutAncestorClass XDP.sdp renewalTime
      renewalTime_positiveSuccessTime .left s q =
      selectedCutAncestorClass XDP.sdp renewalTime renewalTime_positiveSuccessTime
        .left s q' := by
    rw [thinSideCode_coe, thinSideCode_coe] at hc
    dsimp only at hc
    rw [thinTruncationAt_eq_some_selectedCutAncestorClass,
      thinTruncationAt_eq_some_selectedCutAncestorClass] at hc
    exact Option.some.inj hc
  obtain ⟨I⟩ := (selectedCutAncestorClass_eq_iff_geometric_iso XDP.sdp renewalTime
    renewalTime_positiveSuccessTime (sourceAncestorCutRealization_renewal .sdp)
    .left s q q').mp hclass
  exact leftSeamSdpLengths_eq_of_iso I

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The infimum of the coerced finite path lengths, with `⊤` for an empty path set. -/
@[expose] noncomputable def leftSeamSdpTruncationValue (S : Set ℕ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' S)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A finite-code SDP decoder; `0` is only its separate default when the finite code has no
coherent geometric realization. Empty path sets decode to `⊤`. -/
noncomputable def leftSeamSdpTruncationDecoder
    (i t s : ℕ) (c : Option FiniteThinMap) : ℕ∞ := by
  classical
  exact if h : ∃ q : D, TC q.1 s = c then
    leftSeamSdpTruncationValue (leftSeamSdpLengths h.choose i t s)
  else 0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Equal finite codes give equal total truncated shortest-path values, including `⊤`. -/
theorem leftSeamSdpTruncationDecoder_eq (q : D) (i t s : ℕ) :
    leftSeamSdpTruncationDecoder i t s (TC q.1 s) =
      leftSeamSdpTruncationValue (leftSeamSdpLengths q i t s) := by
  classical
  have h : ∃ q' : D, TC q'.1 s = TC q.1 s := ⟨q, rfl⟩
  rw [leftSeamSdpTruncationDecoder, dite_eq_left h]
  exact congrArg leftSeamSdpTruncationValue
    (leftSeamSdpTruncationDetermination_proved h.choose q i t s h.choose_spec)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The total eventual value of the finite-code SDP decoder; its default is used only when
there is no eventual value, which the realization theorem below excludes for coherent code.
A finite-stage code with no coherent realization has the separately documented default above. -/
@[expose] noncomputable def eventualWithTopValue (default : ℕ∞) (u : ℕ → ℕ∞) : ℕ∞ := by
  classical
  exact if h : ∃ z : ℕ∞, ∀ᶠ j in atTop, u j = z then h.choose else default

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
`eventualWithTopValue` agrees with any eventual constant. -/
theorem eventualWithTopValue_eq (default : ℕ∞) {u : ℕ → ℕ∞} {z : ℕ∞}
    (hz : ∀ᶠ j in atTop, u j = z) : eventualWithTopValue default u = z := by
  classical
  have h : ∃ z : ℕ∞, ∀ᶠ j in atTop, u j = z := ⟨z, hz⟩
  rw [eventualWithTopValue, dite_eq_left h]
  obtain ⟨j, hj, hjz⟩ := (h.choose_spec.and hz).exists
  exact hj.symm.trans hjz

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
For a fixed endpoint pair, the finite shortest-path values decrease with the restriction. -/
private theorem leftSeamSdpLengths_mono (q : D) (i t s s' : ℕ) (hss : s ≤ s') :
    leftSeamSdpLengths q i t s ⊆ leftSeamSdpLengths q i t s' := by
  rintro n ⟨hi, ht, p, hp, he⟩
  refine ⟨hi.trans hss, sourceAncestorEdges_mono (W q) (HF q) (HL q) (HT q) (HR q)
    (P q) .left hss ht, p, hp, ?_⟩
  intro e he'
  exact sourceAncestorEdges_mono (W q) (HF q) (HL q) (HT q) (HR q)
    (P q) .left hss (he e he')

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The finite truncation values form an antitone sequence in the restriction index. -/
private theorem leftSeamSdpTruncationValue_antitone (q : D) (i t : ℕ) :
    Antitone (fun s => leftSeamSdpTruncationValue (leftSeamSdpLengths q i t s)) := by
  intro s s' hss
  apply le_sInf
  rintro x ⟨n, hn, rfl⟩
  exact sInf_le ⟨n, leftSeamSdpLengths_mono q i t s s' hss hn, rfl⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The left seam SDP decoder depends only on the code and chosen coherent realization's
truncation values, and returns the eventual shortest-path length or `⊤` if unreachable. -/
@[expose] noncomputable def leftSeamSdpDecoder
    (c : ThinCode) (i t : ℕ) : ℕ∞ :=
  eventualWithTopValue 0 (fun s => leftSeamSdpTruncationDecoder i t s (c s))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every coherent code's truncation distances are eventually constant, hence its decoder is the
eventual truncation value. The `WithTop` value remains `⊤` when no path exists. -/
theorem leftSeamSdpDecoder_realization (q : D) (i t : ℕ) :
    ∃ N, ∀ s, N ≤ s →
      leftSeamSdpTruncationDecoder i t s (TC q.1 s) = leftSeamSdpDecoder (TC q.1) i t := by
  have hanti : Antitone (fun s => leftSeamSdpTruncationDecoder i t s (TC q.1 s)) := by
    intro s s' hss
    change leftSeamSdpTruncationDecoder i t s' (TC q.1 s') ≤
      leftSeamSdpTruncationDecoder i t s (TC q.1 s)
    rw [leftSeamSdpTruncationDecoder_eq q i t s',
      leftSeamSdpTruncationDecoder_eq q i t s]
    exact leftSeamSdpTruncationValue_antitone q i t hss
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨N, fun s hs => ?_⟩
  have hev : ∀ᶠ s in atTop,
      leftSeamSdpTruncationDecoder i t s (TC q.1 s) =
        leftSeamSdpTruncationDecoder i t N (TC q.1 N) :=
    (eventually_ge_atTop N).mono (fun s hs => (hN s hs).symm)
  rw [leftSeamSdpDecoder, eventualWithTopValue_eq 0 hev]
  exact (hN s hs).symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The total decoder is invariant under changing the coherent realization of every finite code. -/
theorem leftSeamSdpDecoder_eq_of_realizations (q q' : D)
    (h : ∀ s, TC q.1 s = TC q'.1 s) (i t : ℕ) :
    leftSeamSdpDecoder (TC q.1) i t = leftSeamSdpDecoder (TC q'.1) i t := by
  change eventualWithTopValue 0
      (fun s => leftSeamSdpTruncationDecoder i t s (TC q.1 s)) =
    eventualWithTopValue 0
      (fun s => leftSeamSdpTruncationDecoder i t s (TC q'.1 s))
  apply congrArg (eventualWithTopValue 0)
  funext s
  rw [leftSeamSdpTruncationDecoder_eq q i t s,
    leftSeamSdpTruncationDecoder_eq q' i t s]
  exact congrArg leftSeamSdpTruncationValue
    (leftSeamSdpTruncationDetermination_proved q q' i t s (h s))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Eventual values of measurable `WithTop ℕ` functions are measurable. -/
theorem measurable_eventualWithTopValue {Ω : Type*} [MeasurableSpace Ω]
    (default : ℕ∞) (f : ℕ → Ω → ℕ∞) (hf : ∀ j, Measurable (f j)) :
    Measurable (fun ω => eventualWithTopValue default (fun j => f j ω)) := by
  classical
  refine measurable_to_countable' (fun z => ?_)
  have he : (fun ω => eventualWithTopValue default (fun j => f j ω)) ⁻¹' {z} =
      {ω | ∀ᶠ j in atTop, f j ω = z} ∪
        ({ω | ¬ ∃ y : ℕ∞, ∀ᶠ j in atTop, f j ω = y} ∩ {ω : Ω | default = z}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    by_cases h : ∃ y : ℕ∞, ∀ᶠ j in atTop, f j ω = y
    · obtain ⟨y, hy⟩ := h
      rw [eventualWithTopValue_eq default hy]
      constructor
      · intro hyz
        exact Or.inl (hy.mono (fun j hj => hj.trans hyz))
      · rintro (hz | ⟨hn, _⟩)
        · exact (eventualWithTopValue_eq default hy).symm.trans
            (eventualWithTopValue_eq default hz)
        · exact (hn ⟨y, hy⟩).elim
    · rw [show eventualWithTopValue default (fun j => f j ω) = default from
        dite_eq_right h]
      constructor
      · intro hd
        exact Or.inr ⟨h, hd⟩
      · rintro (hz | ⟨_, hd⟩)
        · exact (h ⟨z, hz⟩).elim
        · exact hd
  rw [he]
  have hset (z : ℕ∞) : MeasurableSet {ω | ∀ᶠ j in atTop, f j ω = z} := by
    have hh : {ω | ∀ᶠ j in atTop, f j ω = z} =
        ⋃ N : ℕ, ⋂ j : ℕ, ⋂ (_ : N ≤ j), {ω | f j ω = z} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_atTop]
    rw [hh]
    exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun j =>
      MeasurableSet.iInter (fun _ => measurableSet_eq_fun (hf j) measurable_const)))
  have hconst : MeasurableSet {ω | ∃ z : ℕ∞, ∀ᶠ j in atTop, f j ω = z} := by
    have hh : {ω | ∃ z : ℕ∞, ∀ᶠ j in atTop, f j ω = z} =
        ⋃ z : ℕ∞, {ω | ∀ᶠ j in atTop, f j ω = z} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hh]
    exact MeasurableSet.iUnion hset
  have hdefault : MeasurableSet {ω : Ω | default = z} := by
    by_cases h : default = z <;> simp [h]
  exact (hset z).union (hconst.compl.inter hdefault)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Each coordinate of the eventual SDP decoder is measurable. -/
theorem measurable_leftSeamSdpDecoder (i t : ℕ) :
    Measurable (fun c : ThinCode => leftSeamSdpDecoder c i t) := by
  apply measurable_eventualWithTopValue 0
  intro s
  have hm : Measurable (fun c : Option FiniteThinMap =>
      leftSeamSdpTruncationDecoder i t s c) := measurable_from_top
  exact hm.comp (measurable_pi_apply s)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The joint decoder is measurable into its product sigma algebra. -/
theorem measurable_leftSeamSdpDecoder_joint :
    Measurable (leftSeamSdpDecoder : ThinCode → ℕ → ℕ → ℕ∞) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro t
  exact measurable_leftSeamSdpDecoder i t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Attainable raw path lengths in the H-image of the hatted closed left side, between the
hatted outer-boundary vertex and the hatted seam vertex. -/
@[expose] noncomputable def leftSeamSdpRawPathLengths
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (q : D) (i t : ℕ) : Set ℕ :=
  {n | ∃ p : Path
      (⟨hatLimitVertexMap w h (LB q i)⟩ : PresentVertex w)
      ⟨hatLimitVertexMap w h ((P q).initial t).1.id⟩,
    p.length = n ∧ ∀ e ∈ pathEdgeList p,
      e ∈ hatLimitEdgeMap w h ''
        sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) .left}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Open path-lifting step: every raw path in the H-image of the hatted closed left side
lifts, with its length, into a finite geometric ancestor restriction. This is not assumed. -/
@[expose] def LeftSeamSdpRawPathLift : Prop :=
  ∀ (w : ℕ → Fin 3) (h : HasFlowLineHits w) (q : D),
    (W q) = hatCodes w h → ∀ i t n : ℕ,
    ∀ p : Path
      (⟨hatLimitVertexMap w h (LB q i)⟩ : PresentVertex w)
      ⟨hatLimitVertexMap w h ((P q).initial t).1.id⟩,
    p.length = n →
    (∀ e ∈ pathEdgeList p,
      e ∈ hatLimitEdgeMap w h ''
        sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) .left) →
    ∃ s, i ≤ s ∧ (P q).edge t ∈ AE q s ∧
      ∃ r : Path (⟨LB q i⟩ : PresentVertex (W q))
        ⟨((P q).initial t).1.id⟩,
        r.length = n ∧ ∀ e ∈ pathEdgeList r, e ∈ AE q s

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw H-image SDP agrees with the code decoder via the bottom/top-valued infimum of
attainable finite path lengths. Empty raw sets contribute `⊤`, including at `i = 1`, `t = 0`.
Endpoints are the hatted carrier's own boundary and seam vertices, independent of their -/
@[expose] def LeftSeamSdpRawIdentification : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : D),
      q.1 = integrateCodes (hatLawCodes ω) ∧ (W q) = (hatCodes w h) ∧
      ∀ i t : ℕ,
        leftSeamSdpDecoder (Tldp .left (integrateCodes (hatLawCodes ω))) i t =
          leftLengthMin (leftSeamSdpRawPathLengths w h q i t)

end DirectedDistances.Recursive
