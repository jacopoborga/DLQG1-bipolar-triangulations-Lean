module

public import DirectedDistances.Recursive.BusemannRightSideLocalization
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
  selectedCutCoherentDomain XDP.ldp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HL" q => sourceAncestor_left_nonneg
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HT" q => sourceAncestor_left_transient
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "HR" q => sourceAncestor_right_unbounded
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
local notation "P" q => sourceAncestorPath
  XDP.ldp renewalTime renewalTime_positiveSuccessTime q
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
  geometricAncestorRelation XDP.ldp renewalTime renewalTime_positiveSuccessTime
    ThinMapSide.left s q
local notation "Iso" => fun (q q' : D) (s : ℕ) =>
  GeometricAncestorMarkedIso XDP.ldp renewalTime renewalTime_positiveSuccessTime
    ThinMapSide.left s q q'
local notation "TC" =>
  thinSideCode XDP.ldp renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
local notation "Tldp" =>
  thinSideCode XDP.ldp renewalTime renewalTime_positiveSuccessTime

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
@[expose] def leftSeamLdpLengths (q : D) (i t s : ℕ) : Set ℕ :=
  {n | i ≤ s ∧ (P q).edge t ∈ AE q s ∧
    ∃ p : Path (⟨LB q i⟩ : PresentVertex (W q))
      ⟨((P q).initial t).1.id⟩,
      p.length = n ∧ ∀ e ∈ pathEdgeList p, e ∈ AE q s}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A marked isomorphism preserves all finite directed path lengths between the left boundary
and seam marks, including when either mark is absent. -/
private theorem leftSeamLdpLengths_eq_of_iso {q q' : D} {s i t : ℕ}
    (I : Iso q q' s) :
    leftSeamLdpLengths q i t s = leftSeamLdpLengths q' i t s := by
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
Equal left finite codes preserve the LDP length sets between their marked endpoints. -/
theorem leftSeamLdpTruncationDetermination_proved (q q' : D) (i t s : ℕ)
    (hc : TC q.1 s = TC q'.1 s) :
    leftSeamLdpLengths q i t s = leftSeamLdpLengths q' i t s := by
  have hclass : selectedCutAncestorClass XDP.ldp renewalTime
      renewalTime_positiveSuccessTime .left s q =
      selectedCutAncestorClass XDP.ldp renewalTime renewalTime_positiveSuccessTime
        .left s q' := by
    rw [thinSideCode_coe, thinSideCode_coe] at hc
    dsimp only at hc
    rw [thinTruncationAt_eq_some_selectedCutAncestorClass,
      thinTruncationAt_eq_some_selectedCutAncestorClass] at hc
    exact Option.some.inj hc
  obtain ⟨I⟩ := (selectedCutAncestorClass_eq_iff_geometric_iso XDP.ldp renewalTime
    renewalTime_positiveSuccessTime (sourceAncestorCutRealization_renewal .ldp)
    .left s q q').mp hclass
  exact leftSeamLdpLengths_eq_of_iso I

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integer encoding of a finite path-length set uses a negative sentinel when it is empty,
so an unreachable endpoint pair is not encoded as the length zero. -/
@[expose] noncomputable def leftSeamLdpTruncationValue (S : Set ℕ) : ℤ := by
  classical
  exact if h : S.Nonempty then (sSup S : ℕ) else -1

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The integer LDP length in a finite left truncation, total on absent code values. -/
noncomputable def leftSeamLdpTruncationDecoder
    (i t s : ℕ) (c : Option FiniteThinMap) : ℤ := by
  classical
  exact if h : ∃ q : D, TC q.1 s = c then
    leftSeamLdpTruncationValue (leftSeamLdpLengths h.choose i t s)
  else 0

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every coherent realization of a finite left code gives the same decoded length. -/
theorem leftSeamLdpTruncationDecoder_eq (q : D) (i t s : ℕ) :
    leftSeamLdpTruncationDecoder i t s (TC q.1 s) =
      leftSeamLdpTruncationValue (leftSeamLdpLengths q i t s) := by
  classical
  have h : ∃ q' : D, TC q'.1 s = TC q.1 s := ⟨q, rfl⟩
  rw [leftSeamLdpTruncationDecoder, dite_eq_left h]
  exact congrArg leftSeamLdpTruncationValue
    (leftSeamLdpTruncationDetermination_proved h.choose q i t s h.choose_spec)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The total left seam decoder uses the eventual finite marked-truncation LDP value. -/
@[expose] noncomputable def leftSeamLdpDecoder
    (c : ThinCode) (i t : ℕ) : ℤ :=
  eventualIntValue 0 (fun s => leftSeamLdpTruncationDecoder i t s (c s))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
For each fixed pair of endpoint indices the left seam decoder is measurable. -/
theorem measurable_leftSeamLdpDecoder (i t : ℕ) :
    Measurable (fun c : ThinCode => leftSeamLdpDecoder c i t) := by
  apply measurable_eventualIntValue 0
  intro s
  have hm : Measurable (fun c : Option FiniteThinMap =>
      leftSeamLdpTruncationDecoder i t s c) := measurable_from_top
  exact hm.comp (measurable_pi_apply s)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The whole two-index decoder is measurable into its product sigma algebra. -/
theorem measurable_leftSeamLdpDecoder_joint :
    Measurable (leftSeamLdpDecoder : ThinCode → ℕ → ℕ → ℤ) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro t
  exact measurable_leftSeamLdpDecoder i t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Attainable raw path lengths in the H-image of the hatted closed left side, between the
hatted outer-boundary vertex and the hatted seam vertex. -/
@[expose] noncomputable def leftSeamRawPathLengths
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
@[expose] def LeftSeamRawPathLift : Prop :=
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
The raw H-image LDP has an attained finite maximum and agrees with the code decoder.
Endpoints are the hatted carrier's own boundary and seam vertices, independent of their
separate beta-index identification.
FALSE as stated (empty raw length set at i = 1, t = 0): refuted by
not_leftSeamLdpRawIdentification in Recursive/HattedLeftSeamDecoderExists.lean, which proves
the ⊥-valued correction LeftSeamLdpRawIdentificationWithBottom. -/
@[expose] def LeftSeamLdpRawIdentification : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∃ (h : HasFlowLineHits w) (q : D),
      q.1 = integrateCodes (hatLawCodes ω) ∧ (W q) = (hatCodes w h) ∧
      ∀ i t : ℕ, ∃ n : ℕ,
        IsGreatest (leftSeamRawPathLengths w h q i t) n ∧
        leftSeamLdpDecoder (Tldp .left (integrateCodes (hatLawCodes ω))) i t =
          (n : ℤ)

end DirectedDistances.Recursive
