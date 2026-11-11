module

public import DirectedDistances.PaperProofs.Section5.GeoInftySideVertices
import DirectedDistances.KMSW.RawHatLinearOrder
import DirectedDistances.KMSW.HatBoundaryFacts

/-! transport of the nonnegative right-side cells along the hatted embedding.
The individual relation tags are proved separately and assembled into a marked
geometric isomorphism. The indexed exterior boundary is transported through
the record-edge creation times, retaining edge identity and multiedges. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "V" => boundaryGluingHatVertexMap W h k hτ
local notation "E" => boundaryGluingHatEdgeMap W h k hτ

/-- Helper toward Lemma 5.5: the hatted vertex embedding restricted to the
right-side carriers is a bijection. -/
@[expose] noncomputable def boundaryGluing_nonneg_right_vertexEquiv :
    (Q).vertices ≃ (S).vertices :=
  Equiv.ofBijective (fun v => ⟨V v.val, by
    rw [boundaryGluing_nonneg_right_vertices hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨v.val, v.property, rfl⟩⟩)
    ⟨fun a b hab => Subtype.ext (boundaryGluingHatVertexMap_injective W h k hτ
      (congrArg Subtype.val hab)), by
      rintro ⟨v, hv⟩
      rw [boundaryGluing_nonneg_right_vertices hτ hp P hqMode Tpath hfin hleft hk] at hv
      obtain ⟨a, ha, hva⟩ := hv
      exact ⟨⟨a, ha⟩, Subtype.ext hva⟩⟩

/-- Helper toward Lemma 5.5: both darts of each retained geometric edge
are transported, with no presence filter. -/
@[expose] noncomputable def boundaryGluing_nonneg_right_dartEquiv :
    {d : ℕ × Bool // d.1 ∈ (Q).edges} ≃ {d : ℕ × Bool // d.1 ∈ (S).edges} :=
  Equiv.ofBijective (fun d => ⟨(E d.val.1, d.val.2), by
    rw [(boundaryGluing_nonneg_side_identities W h k hτ longest hp P
      hqMode Tpath hfin hleft hk).1]
    exact ⟨d.val.1, d.property, rfl⟩⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ
        (congrArg (fun d => d.val.1) hab)) (congrArg (fun d => d.val.2) hab), by
      rintro ⟨d, hd⟩
      rw [(boundaryGluing_nonneg_side_identities W h k hτ longest hp P
        hqMode Tpath hfin hleft hk).1] at hd
      obtain ⟨e, he, hed⟩ := hd
      exact ⟨⟨(e, d.2), he⟩, Subtype.ext (Prod.ext hed rfl)⟩⟩

/-- Helper toward Lemma 5.5: equivalence of all right-side cells, using
the hatted vertex map and the hatted dart map restricted to their carriers. -/
@[expose] noncomputable def boundaryGluing_nonneg_right_cellEquiv :
    GeometricSideCell Q ≃ GeometricSideCell S :=
  Equiv.sumCongr
    (boundaryGluing_nonneg_right_vertexEquiv hτ hp P hqMode Tpath hfin hleft hk)
    (boundaryGluing_nonneg_right_dartEquiv hτ hp P hqMode Tpath hfin hleft hk)

local notation "Φ" => boundaryGluing_nonneg_right_cellEquiv
  hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the cell equivalence preserves the vertex tag. -/
theorem boundaryGluing_nonneg_right_vertex_iff (u v : GeometricSideCell Q) :
    geometricSideRelation Q .vertex u v ↔ geometricSideRelation S .vertex (Φ u) (Φ v) := by
  cases u <;> cases v <;> rfl

/-- Helper toward Lemma 5.5: the cell equivalence preserves the root tag. -/
theorem boundaryGluing_nonneg_right_root_iff (u v : GeometricSideCell Q) :
    geometricSideRelation Q .root u v ↔ geometricSideRelation S .root (Φ u) (Φ v) := by
  cases u with
  | inl a =>
    change a.val = 0 ↔ V a.val = boundaryVertex (shiftedStream W 0) h k
    rw [← boundaryGluingHatVertexMap_zero hτ]
    exact (boundaryGluingHatVertexMap_injective W h k hτ).eq_iff.symm
  | inr d => cases v <;> rfl

/-- Helper toward Lemma 5.5: both endpoint identities in the decoded stream,
without any assumption of directed presence. -/
theorem boundaryGluing_nonneg_right_endpoints (e : ℕ) :
    (S).west (E e) = V ((Q).west e) ∧ (S).east (E e) = V ((Q).east e) := by
  change edgeWest (shiftedStream W 0) (E e) =
      V (edgeWest (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e) ∧
    edgeEast (shiftedStream W 0) (E e) =
      V (edgeEast (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e)
  rw [boundaryGluing_decoded_stream W h k hτ]
  exact boundaryGluing_hat_edge_endpoints W h k hτ e

/-- Helper toward Lemma 5.5: incidence is preserved for both darts,
including all geometric edges without a presence restriction. -/
theorem boundaryGluing_nonneg_right_incident_iff (u v : GeometricSideCell Q) :
    geometricSideRelation Q .incident u v ↔
      geometricSideRelation S .incident (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v with
    | inr e => rfl
    | inl a =>
      obtain ⟨⟨e, b⟩, he⟩ := d
      cases b with
      | false =>
        change (Q).west e = a.val ↔ (S).west (E e) = V a.val
        rw [(boundaryGluing_nonneg_right_endpoints hτ hp P hqMode e).1]
        exact (boundaryGluingHatVertexMap_injective W h k hτ).eq_iff.symm
      | true =>
        change (Q).east e = a.val ↔ (S).east (E e) = V a.val
        rw [(boundaryGluing_nonneg_right_endpoints hτ hp P hqMode e).2]
        exact (boundaryGluingHatVertexMap_injective W h k hτ).eq_iff.symm

/-- Helper toward Lemma 5.5: the hatted dart embedding commutes with
opposition, with edge identity and the side bit both retained. -/
theorem boundaryGluing_nonneg_right_opposite_iff (u v : GeometricSideCell Q) :
    geometricSideRelation Q .opposite u v ↔
      geometricSideRelation S .opposite (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v with
    | inl a => rfl
    | inr e =>
      change (d.val.1, !d.val.2) = e.val ↔ (E d.val.1, !d.val.2) = (E e.val.1, e.val.2)
      rw [Prod.ext_iff, Prod.ext_iff]
      exact and_congr (boundaryGluingHatEdgeMap_injective W h k hτ).eq_iff.symm Iff.rfl

/-- Helper toward Lemma 5.5: every hatted geometric edge is present in
the decoded stream and its run-zero image is present. -/
theorem boundaryGluing_nonneg_right_present (e : ℕ) :
    e ∈ (Q).present ∧ E e ∈ (S).present := by
  have hh := hatCodes_edge_present (boundaryGluingFutureStream W h k) hτ e
  have hi := (shiftHat_edge_incidence (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k) hτ e).2.2 hh
  change EdgePresent _ _ at hi
  dsimp only [boundaryGluingHatEdgeMap, Function.comp_apply]
  rw [boundaryGluingEdgeMap_eq_shift W h k]
  refine ⟨?_, hi⟩
  change EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e
  rw [boundaryGluing_decoded_stream W h k hτ]
  exact hh

/-- Helper toward Lemma 5.5: directed presence and forward orientation
are both preserved by the cell equivalence. -/
theorem boundaryGluing_nonneg_right_oriented_iff (u v : GeometricSideCell Q) :
    geometricSideRelation Q .oriented u v ↔
      geometricSideRelation S .oriented (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    change (d.val.1 ∈ (Q).present ∧ d.val.2 = false) ↔
      (E d.val.1 ∈ (S).present ∧ d.val.2 = false)
    have hpresent := boundaryGluing_nonneg_right_present hτ hp P hqMode d.val.1
    exact and_congr (iff_of_true hpresent.1 hpresent.2) Iff.rfl

/-- Helper toward Lemma 5.5: the finite-only target tag is empty on
both whole geometric sides. -/
theorem boundaryGluing_nonneg_right_target_iff (u v : GeometricSideCell Q) :
    geometricSideRelation Q .target u v ↔
      geometricSideRelation S .target (Φ u) (Φ v) := by
  cases u <;> cases v <;> rfl

/-- Helper toward Lemma 5.5: first-return times enumerate the image darts
in order without skipping any image dart. -/
private theorem hattedSide_orderedImageScan {α β : Type*} (σ : α → α) (τ : β → β)
    (I : α → β)
    (hret : ∀ x, ∃ n : ℕ, 0 < n ∧ τ^[n] (I x) = I (σ x) ∧
      ∀ j : ℕ, 0 < j → j < n → τ^[j] (I x) ∉ Set.range I)
    (d : α) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ N 0 = 0 ∧
      (∀ n, τ^[N n] (I d) = I (σ^[n] d)) ∧
      (∀ n j, j < N n →
        (τ^[j] (I d) ∈ Set.range I ↔ ∃ i < n, j = N i)) := by
  classical
  let r (n : ℕ) := (hret (σ^[n] d)).choose
  have hr (n : ℕ) : 0 < r n ∧
      τ^[r n] (I (σ^[n] d)) = I (σ (σ^[n] d)) ∧
      ∀ j : ℕ, 0 < j → j < r n → τ^[j] (I (σ^[n] d)) ∉ Set.range I :=
    (hret (σ^[n] d)).choose_spec
  let N : ℕ → ℕ := fun n => Nat.rec 0 (fun i acc => acc + r i) n
  have hN0 : N 0 = 0 := rfl
  have hNs (n : ℕ) : N (n + 1) = N n + r n := rfl
  have hmono : StrictMono N := strictMono_nat_of_lt_succ fun n => by
    rw [hNs]
    have := (hr n).1
    omega
  have hmap (n : ℕ) : τ^[N n] (I d) = I (σ^[n] d) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hNs, Nat.add_comm, Function.iterate_add_apply, ih,
        (hr n).2.1, Function.iterate_succ_apply']
  refine ⟨N, hmono, hN0, hmap, ?_⟩
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    constructor
    · intro hm
      rcases Nat.lt_trichotomy j (N n) with hlt | heq | hgt
      · obtain ⟨i, hi, he⟩ := (ih j hlt).1 hm
        exact ⟨i, by omega, he⟩
      · exact ⟨n, by omega, heq⟩
      · apply False.elim
        apply (hr n).2.2 (j - N n) (by omega) (by rw [hNs] at hj; omega)
        have he : τ^[j - N n] (I (σ^[n] d)) = τ^[j] (I d) := by
          rw [← hmap, ← Function.iterate_add_apply, Nat.sub_add_cancel hgt.le]
        rw [he]
        exact hm
    · rintro ⟨i, _, rfl⟩
      rw [hmap]
      exact ⟨σ^[i] d, rfl⟩

/-- Helper toward Lemma 5.5: a proved first-return embedding preserves
the rotation relation restricted to any further subset. -/
private theorem hattedSide_restrictedRotation_iff {α β : Type*}
    (σ : α → α) (τ : β → β) (I : α → β) (hinj : Function.Injective I)
    (hret : ∀ x, ∃ n : ℕ, 0 < n ∧ τ^[n] (I x) = I (σ x) ∧
      ∀ j : ℕ, 0 < j → j < n → τ^[j] (I x) ∉ Set.range I)
    (A : Set α) (d e : α) :
    (∃ n : ℕ, 0 < n ∧ σ^[n] d = e ∧
      ∀ j : ℕ, 0 < j → j < n → σ^[j] d ∉ A) ↔
    (∃ n : ℕ, 0 < n ∧ τ^[n] (I d) = I e ∧
      ∀ j : ℕ, 0 < j → j < n → τ^[j] (I d) ∉ I '' A) := by
  obtain ⟨N, hmono, hzero, hmap, hhits⟩ := hattedSide_orderedImageScan σ τ I hret d
  have hpos (i : ℕ) : 0 < N i ↔ 0 < i := by
    calc
      0 < N i ↔ N 0 < N i := by rw [hzero]
      _ ↔ 0 < i := hmono.lt_iff_lt
  have hlower (n : ℕ) : n ≤ N n := by
    induction n with
    | zero => omega
    | succ n ih =>
      have := hmono (show n < n + 1 by omega)
      omega
  constructor
  · rintro ⟨n, hn, he, hgap⟩
    refine ⟨N n, (hpos n).mpr hn, (hmap n).trans (congrArg I he), ?_⟩
    intro j hj hjn hmem
    obtain ⟨a, ha, haj⟩ := hmem
    obtain ⟨i, hi, hji⟩ := (hhits n j hjn).mp ⟨a, haj⟩
    have hipos : 0 < i := (hpos i).mp (hji ▸ hj)
    apply hgap i hipos hi
    have hai : a = σ^[i] d := hinj (haj.trans (hji ▸ hmap i))
    exact hai ▸ ha
  · rintro ⟨n, hn, he, hgap⟩
    have hnb : n < N (n + 1) := by have := hlower (n + 1); omega
    obtain ⟨i, _, hni⟩ := (hhits (n + 1) n hnb).mp ⟨e, he.symm⟩
    refine ⟨i, (hpos i).mp (hni ▸ hn), ?_, ?_⟩
    · apply hinj
      exact (hmap i).symm.trans (hni ▸ he)
    · intro j hj hji hjA
      apply hgap (N j) ((hpos j).mpr hj)
      · rw [hni]
        exact hmono hji
      · exact ⟨σ^[j] d, hjA, (hmap j).symm⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: induced rotation agrees on the hatted and
actual right sides, after restriction to their exact geometric edge carriers. -/
theorem boundaryGluing_nonneg_right_rotation (d e : ℕ × Bool) :
    (Q).rotation d e ↔ (S).rotation (E d.1, d.2) (E e.1, e.2) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let z := hatCodes u hτ
  let hz := hatCodes_inducedFiniteIncidence u hτ hfin
  let I : (ℕ × Bool) → ℕ × Bool := fun a => (hatLimitEdgeMap u hτ a.1, a.2)
  let J : (ℕ × Bool) → ℕ × Bool := fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
  let D : (ℕ × Bool) → ℕ × Bool := fun a => (E a.1, a.2)
  have hJinj : Function.Injective J := by
    intro a b hab
    have hb := congrArg (fun a : ℕ × Bool => a.2) hab
    exact Prod.ext (boundaryGluingEdgeMap_injective W h k (congrArg Prod.fst hab))
      hb
  have hDinj : Function.Injective D := by
    intro a b hab
    have hb := congrArg (fun a : ℕ × Bool => a.2) hab
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ (congrArg Prod.fst hab))
      hb
  have hJ : J = fun a : ℕ × Bool => (kmswShiftEdgeMapAll w t a.1 a.1, a.2) := by
    funext a
    exact Prod.ext (boundaryGluingEdgeMap_eq_shift W h k a.1) rfl
  have hretJ (a : ℕ × Bool) : ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (J a) = J (kmswInfRot u hfin a) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (J a) ∉ Set.range J := by
    rw [hJ]
    exact shiftInfRot_firstReturn w t hfin (H.1 0) a
  have hret := hatExit_induced_rotation_comp (kmswInfRot z hz)
    (kmswInfRot u hfin) (kmswInfRot w (H.1 0)) I J hJinj
    (hatInfRot_firstReturn u hτ hfin) hretJ
  have hcomp : J ∘ I = D := rfl
  rw [hcomp] at hret
  let A : Set (ℕ × Bool) := {a | a.1 ∈ (Q).edges}
  have hset : D '' A = {a : ℕ × Bool | a.1 ∈ (S).edges} := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      change E b.1 ∈ (S).edges
      rw [(boundaryGluing_nonneg_side_identities W h k hτ longest hp P
        hqMode Tpath hfin hleft hk).1]
      exact ⟨b.1, hb, rfl⟩
    · intro ha
      change a.1 ∈ (S).edges at ha
      rw [(boundaryGluing_nonneg_side_identities W h k hτ longest hp P
        hqMode Tpath hfin hleft hk).1] at ha
      obtain ⟨b, hb, hba⟩ := ha
      exact ⟨(b, a.2), hb, Prod.ext hba rfl⟩
  have hr := hattedSide_restrictedRotation_iff (kmswInfRot z hz : _ → _)
    (kmswInfRot w (H.1 0) : _ → _) D hDinj hret A d e
  rw [hset] at hr
  have hc := boundaryGluing_decoded_stream W h k hτ
  change boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)) = z at hc
  have hrot_congr (a b : ℕ → Fin 3) (ha : KMSWFiniteIncidence a)
      (hb : KMSWFiniteIncidence b) (hab : a = b) :
      kmswInfRot a ha = kmswInfRot b hb := by
    subst b
    rfl
  have hrotEq := hrot_congr _ _
    (sourceAncestor_finite_incidence (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩) hz hc
  change (∃ n : ℕ, 0 < n ∧
      (kmswInfRot (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W)))
        (sourceAncestor_finite_incidence (if longest then XDP.ldp else XDP.sdp)
          renewalTime renewalTime_positiveSuccessTime
          ⟨boundaryFutureHattedPath k W, hqMode⟩) : _ → _)^[n] d = e ∧
      ∀ j : ℕ, 0 < j → j < n → _ ∉ (Q).edges) ↔ _
  rw [hrotEq]
  exact hr

/-- Helper toward Lemma 5.5: the cell equivalence preserves the rotation tag. -/
theorem boundaryGluing_nonneg_right_rotation_iff (u v : GeometricSideCell Q) :
    geometricSideRelation Q .rotation u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v with
    | inl a => rfl
    | inr e =>
      exact boundaryGluing_nonneg_right_rotation
        hτ hp P hqMode Tpath hfin hleft hk d.val e.val

/-- Helper toward Lemma 5.5: the old and new active edges in a creation
triangle have the same east endpoint exactly in the left-step branch. -/
private theorem hattedSide_record_east_eq_iff (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    edgeEast w (stageTriangleRecord w j).1 =
      edgeEast w (stageTriangleRecord w j).2.1 ↔ w j.val = 0 := by
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  have hb := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
  rw [← (edge_endpoints_eq w hb.1).2, ← (edge_endpoints_eq w hb.2.1).2]
  have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
  have hne := ne_of_lt ha
  have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by
    omega
  have hv := (kmswStage_endpoints_lt_nextVertex w j.val _ ha).2
  rcases j.property with h0 | h1
  · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, h0, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, hp, State.addEdge, hne, hne']
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, h1, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge, hne, hne', ne_of_lt hv]

/-- Helper toward Lemma 5.5: the stored oriented word and the creation
word have the same darts, including the cyclic shift in existing-left steps. -/
private theorem hattedSide_creation_oriented_mem (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (d : ℕ × Bool) :
    d ∈ triangleOrientedDarts w (stageTriangleRecord w j) ↔
      d ∈ stageTriangleDartList w j := by
  unfold triangleOrientedDarts
  rcases j.property with h0 | h1
  · rw [ite_eq_left ((hattedSide_record_east_eq_iff w j).mpr h0)]
    cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple,
        h0, hp, or_comm, or_left_comm, or_assoc]
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    rw [ite_eq_right (fun he => h0 ((hattedSide_record_east_eq_iff w j).mp he))]
    simp only [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple,
      h0, ↓reduceIte]

/-- Helper toward Lemma 5.5: every creation triangle has an edge outside
any infinite present path. The old and new active edges share an endpoint,
whereas a directed path uses at most one incoming and one outgoing edge. -/
private theorem hattedSide_triangle_off_path (w : ℕ → Fin 3)
    (hf : KMSWFiniteIncidence w) {v : ℕ} (R : InfinitePresentPath w ⟨v⟩)
    (j : TriangleCreationTime w) :
    ∃ d ∈ stageTriangleDartList w j, d.1 ∉ Set.range R.edge := by
  classical
  have hW := infinitePresentPath_west_injective hf
    (fun n => ⟨_, (monotone_family_all w n).choose_spec⟩) R
  have hE : Function.Injective (fun i => edgeEast w (R.edge i)) := by
    intro a b hab
    change edgeEast w (R.edge a) = edgeEast w (R.edge b) at hab
    have he (i : ℕ) : edgeEast w (R.edge i) = edgeWest w (R.edge (i + 1)) :=
      (R.edge_incoming_at_succ w i).2.trans (R.edge_outgoing_at_initial w (i + 1)).2.symm
    rw [he, he] at hab
    have := hW hab
    omega
  let t := stageTriangleRecord w j
  have hne : t.1 ≠ t.2.1 := by
    have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
    rcases j.property with h0 | h1
    · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
        simpa only [t, stageTriangleRecord, h0, ↓reduceIte, hp] using ne_of_lt ha
    · have h0 : w j.val ≠ 0 := by rw [h1]; decide
      simpa only [t, stageTriangleRecord, h0, ↓reduceIte] using ne_of_lt ha
  have hold : (t.1, false) ∈ stageTriangleDartList w j := by
    apply (hattedSide_creation_oriented_mem w j _).mp
    unfold triangleOrientedDarts
    split <;> exact List.mem_cons_self
  have hnew : (t.2.1, true) ∈ stageTriangleDartList w j := by
    apply (hattedSide_creation_oriented_mem w j _).mp
    unfold triangleOrientedDarts
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false, t, Prod.mk.injEq,
      and_true, true_or, or_true]
  by_contra hn
  have hall : ∀ d ∈ stageTriangleDartList w j, d.1 ∈ Set.range R.edge := by
    intro d hd
    by_contra hnot
    exact hn ⟨d, hd, hnot⟩
  obtain ⟨a, ha⟩ := hall _ hold
  obtain ⟨b, hb⟩ := hall _ hnew
  apply hne
  have heq : a = b := by
    by_cases h0 : w j.val = 0
    · apply hE
      change edgeEast w (R.edge a) = edgeEast w (R.edge b)
      rw [ha, hb]
      exact (hattedSide_record_east_eq_iff w j).mpr h0
    · apply hW
      change edgeWest w (R.edge a) = edgeWest w (R.edge b)
      rw [ha, hb]
      have h1 : w j.val = 1 := j.property.resolve_left h0
      obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
      have hbounds := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
      rw [← (edge_endpoints_eq w hbounds.1).1, ← (edge_endpoints_eq w hbounds.2.1).1]
      have hact := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
      have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by
        omega
      simp [stageTriangleRecord, h1, kmswStage, kmswStep,
        kmswCodeStep, kmswStepOfStep, State.addEdge, ne_of_lt hact, hne']
  exact ha.symm.trans (heq ▸ hb)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: retention of a geometric edge is reflected
by the hatted embedding, without a directed-presence restriction. -/
theorem boundaryGluing_nonneg_right_edge_iff (e : ℕ) :
    e ∈ (Q).edges ↔ E e ∈ (S).edges := by
  rw [(boundaryGluing_nonneg_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft hk).1]
  constructor
  · exact fun he => ⟨e, he, rfl⟩
  · rintro ⟨a, ha, hae⟩
    exact boundaryGluingHatEdgeMap_injective W h k hτ hae ▸ ha

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a hatted creation triangle maps to a glued
face, and the triangle is retained exactly when that face lies in the actual
open right side. The face and its bordering darts are proved, not assumed. -/
theorem boundaryGluing_nonneg_right_triangle_retained
    (j : TriangleCreationTime (hatCodes (boundaryGluingFutureStream W h k) hτ)) :
    ∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      F.val ⊆ m0GeodesicAmbientRegion W H h ∧
      (∀ d ∈ stageTriangleDartList (hatCodes (boundaryGluingFutureStream W h k) hτ) j,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 (E d.1, d.2)) F) ∧
      ((∀ d ∈ stageTriangleDartList (hatCodes (boundaryGluingFutureStream W h k) hτ) j,
          d.1 ∈ (Q).edges) ↔ F.val ⊆ m0GeodesicSideOpenRegion hp P .right) := by
  let z := hatCodes (boundaryGluingFutureStream W h k) hτ
  have hc := boundaryGluing_decoded_stream W h k hτ
  let j' : TriangleCreationTime
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) :=
    ⟨j.val, by rw [hc]; exact j.property⟩
  let R := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index z j
  let T : HatLocalTri (boundaryGluingFutureStream W h k) hτ :=
    ⟨stageTriangleRecord z j, j.val + 1, hi ▸ List.get_mem _ i⟩
  obtain ⟨F, hFR, hborder⟩ := boundaryGluing_hatTriangle_gluedFace W h k hτ H hp hfin T
  have hb (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList z j) :
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (E d.1, d.2)) F :=
    hborder d ((hattedSide_creation_oriented_mem z j d).mpr hd)
  refine ⟨F, hFR, hb, ?_⟩
  have hedge := boundaryGluing_nonneg_right_edge_iff hτ hp P hqMode Tpath hfin hleft hk
  constructor
  · intro hall
    obtain ⟨d, hd, hoff⟩ := hattedSide_triangle_off_path _
      (sourceAncestor_finite_incidence (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime
        ⟨boundaryFutureHattedPath k W, hqMode⟩) R j'
    have hdz : d ∈ stageTriangleDartList z j := by
      simpa only [stageTriangleDartList, stageTriangleDartTriple, j', hc, z] using hd
    have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
      hp Tpath P hfin hleft
    have hoff' : E d.1 ∉ m0GeodesicEdges P := by
      rintro ⟨a, ha⟩
      apply hoff
      exact ⟨a, boundaryGluingHatEdgeMap_injective W h k hτ ((hid a).symm.trans ha)⟩
    exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hoff'
      d.2 F hFR (hb d hdz) .right).mp ((hedge d.1).mp (hall d hdz))
  · intro hF d hd
    apply (hedge d.1).mpr
    by_cases hs : E d.1 ∈ m0GeodesicEdges P
    · exact (m0GeodesicEdges_subset_both hp P hs).2
    · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hs
        d.2 F hFR (hb d hd) .right).mpr hF

/-- Helper toward Lemma 5.5: the composite hatted dart embedding is a
first-return embedding for the full ambient rotations. -/
private theorem hattedSide_ambient_firstReturn (d : ℕ × Bool) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (E d.1, d.2) =
        (E (kmswInfRot (hatCodes (boundaryGluingFutureStream W h k) hτ)
          (hatCodes_inducedFiniteIncidence _ hτ hfin) d).1,
          (kmswInfRot (hatCodes (boundaryGluingFutureStream W h k) hτ)
            (hatCodes_inducedFiniteIncidence _ hτ hfin) d).2) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (E d.1, d.2) ∉
          Set.range (fun a : ℕ × Bool => (E a.1, a.2)) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let z := hatCodes u hτ
  let I : (ℕ × Bool) → ℕ × Bool := fun a => (hatLimitEdgeMap u hτ a.1, a.2)
  let J : (ℕ × Bool) → ℕ × Bool := fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
  have hJinj : Function.Injective J := by
    intro a b hab
    have hb := congrArg (fun a : ℕ × Bool => a.2) hab
    exact Prod.ext (boundaryGluingEdgeMap_injective W h k (congrArg Prod.fst hab))
      hb
  have hJ : J = fun a : ℕ × Bool => (kmswShiftEdgeMapAll w t a.1 a.1, a.2) := by
    funext a
    exact Prod.ext (boundaryGluingEdgeMap_eq_shift W h k a.1) rfl
  have hretJ (a : ℕ × Bool) : ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (J a) = J (kmswInfRot u hfin a) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (J a) ∉ Set.range J := by
    rw [hJ]
    exact shiftInfRot_firstReturn w t hfin (H.1 0) a
  exact hatExit_induced_rotation_comp (kmswInfRot z
    (hatCodes_inducedFiniteIncidence u hτ hfin)) (kmswInfRot u hfin)
    (kmswInfRot w (H.1 0)) I J hJinj (hatInfRot_firstReturn u hτ hfin) hretJ d

/-- Helper toward Lemma 5.5: an ambient face step whose endpoint is
again an image dart reflects to the hatted face successor. -/
private theorem hattedSide_face_step_reflect (d e : ℕ × Bool)
    (he : kmswInfFaceSucc (shiftedStream W 0) (H.1 0) (E d.1, d.2) =
      (E e.1, e.2)) :
    kmswInfFaceSucc (hatCodes (boundaryGluingFutureStream W h k) hτ)
      (hatCodes_inducedFiniteIncidence _ hτ hfin) d = e := by
  let σ := kmswInfRot (hatCodes (boundaryGluingFutureStream W h k) hτ)
    (hatCodes_inducedFiniteIncidence _ hτ hfin)
  let τ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let D : (ℕ × Bool) → ℕ × Bool := fun a => (E a.1, a.2)
  have hinj : Function.Injective D := by
    intro a b hab
    have hb := congrArg (fun a : ℕ × Bool => a.2) hab
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ
      (congrArg Prod.fst hab)) hb
  have hstep : τ (D e) = D (d.1, !d.2) := by
    change τ.symm (D (d.1, !d.2)) = D e at he
    have hh := congrArg τ he
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm
  obtain ⟨n, hn, hret, hgap⟩ := hattedSide_ambient_firstReturn hτ hfin (H := H) e
  change (τ : _ → _)^[n] (D e) = D (σ e) at hret
  have hn1 : n = 1 := by
    by_contra hne
    exact hgap 1 (by omega) (by omega) ⟨(d.1, !d.2), by
      simpa only [Function.iterate_one] using hstep.symm⟩
  rw [hn1, Function.iterate_one, hstep] at hret
  have hs : (d.1, !d.2) = σ e := hinj hret
  change σ.symm (d.1, !d.2) = e
  rw [hs, Equiv.symm_apply_apply]

/-- Helper toward Lemma 5.5: two faces bordering the same oriented
dart agree, by intersection of their small left wedges. -/
private theorem hattedSide_border_face_unique {δ ν : Type*} {flip : δ → δ}
    {rot : Equiv.Perm δ} {vert : δ → ν} (G : PLDrawing δ ν flip rot vert)
    {F F' : G.Face} {d : δ} (hF : G.dartBorders d F) (hF' : G.dartBorders d F') :
    F = F' := by
  obtain ⟨a, ha, hF⟩ := hF
  obtain ⟨b, hb, hF'⟩ := hF'
  let t := min a b / 2
  have ht : 0 < t := half_pos (lt_min ha hb)
  have hta : t < a := (half_lt_self (lt_min ha hb)).trans_le (min_le_left _ _)
  have htb : t < b := (half_lt_self (lt_min ha hb)).trans_le (min_le_right _ _)
  exact G.faces_eq_of_mem (hF t t ht hta ht hta) (hF' t t ht htb ht htb)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every retained actual face bordering an
image dart reflects to a retained hatted creation triangle. -/
theorem boundaryGluing_nonneg_right_retained_face_reflect (d : ℕ × Bool) :
    (∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (E d.1, d.2)) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp P .right) →
    (∃ j : TriangleCreationTime (hatCodes (boundaryGluingFutureStream W h k) hτ),
      d ∈ stageTriangleDartList (hatCodes (boundaryGluingFutureStream W h k) hτ) j ∧
      ∀ a ∈ stageTriangleDartList (hatCodes (boundaryGluingFutureStream W h k) hτ) j,
        a.1 ∈ (Q).edges) ∧
    kmswInfFaceSucc (shiftedStream W 0) (H.1 0) (E d.1, d.2) =
      (E (kmswInfFaceSucc (hatCodes (boundaryGluingFutureStream W h k) hτ)
        (hatCodes_inducedFiniteIncidence _ hτ hfin) d).1,
        (kmswInfFaceSucc (hatCodes (boundaryGluingFutureStream W h k) hτ)
          (hatCodes_inducedFiniteIncidence _ hτ hfin) d).2) := by
  classical
  rintro ⟨F, hdF, hF⟩
  let w := shiftedStream W 0
  let z := hatCodes (boundaryGluingFutureStream W h k) hτ
  let A := monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  let f := kmswInfFaceSucc z (hatCodes_inducedFiniteIncidence _ hτ hfin)
  let g := kmswInfFaceSucc w (H.1 0)
  let D : (ℕ × Bool) → ℕ × Bool := fun a => (E a.1, a.2)
  have hinj : Function.Injective D := by
    intro a b hab
    have hb := congrArg (fun a : ℕ × Bool => a.2) hab
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ
      (congrArg Prod.fst hab)) hb
  have hFR : F.val ⊆ m0GeodesicAmbientRegion W H h := fun a ha => (hF ha).1
  have hupper : F.val ⊆ {a : ℂ | seamFun w h (H.1 0) a.re < a.im} := by
    rcases WholePlaneM0Drawing.face_side W h hp H F with hu | hl
    · exact hu
    · obtain ⟨a, ha, hface⟩ := F.property
      have ham : a ∈ F.val := hface ▸ mem_connectedComponentIn ha
      have hle : seamFun w h (H.1 0) a.re ≤ a.im := hFR ham
      have hlt : a.im < seamFun w h (H.1 0) a.re := hl ham
      exact False.elim (not_lt_of_ge hle hlt)
  obtain ⟨F0, hF0, hval⟩ := (WholePlaneM0Drawing.m0_face_iff W h hp H F).mp hupper
  have hb (r : ℕ × Bool) : A.dartBorders r F0 ↔
      G.dartBorders (wholePlaneDartι W 0 r) F := by
    exact (PLDrawing.dartBorders_congr A G F0 F
      (WholePlanePastGlueM0Restriction.restrict_arc W h hp H r) hval).symm
  obtain ⟨j0, hlist, hcycle, _⟩ := boundedFace_orbit_is_triangle w (H.1 0) h F0 hF0
  have hforward (r : ℕ × Bool) (hr : A.dartBorders r F0) : A.dartBorders (g r) F0 := by
    apply (Set.ext_iff.mp hcycle (g r)).mpr
    exact ((Set.ext_iff.mp hcycle r).mp hr).apply_right
  have hbackward (r : ℕ × Bool) (hr : A.dartBorders r F0) :
      A.dartBorders (g.symm r) F0 := by
    apply (Set.ext_iff.mp hcycle (g.symm r)).mpr
    exact ((Set.ext_iff.mp hcycle r).mp hr).symm_apply_right
  have himage (r : ℕ × Bool) (hr : A.dartBorders r F0) : ∃ a, D a = r := by
    have he : r.1 ∈ (S).edges := by
      by_cases hs : r.1 ∈ m0GeodesicEdges P
      · exact (m0GeodesicEdges_subset_both hp P hs).2
      · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hs
          r.2 F hFR ((hb r).mp hr) .right).mpr hF
    rw [(boundaryGluing_nonneg_side_identities W h k hτ longest hp P
      hqMode Tpath hfin hleft hk).1] at he
    obtain ⟨a, _, ha⟩ := he
    exact ⟨(a, r.2), Prod.ext ha rfl⟩
  have hpos (a : ℕ × Bool) (ha : A.dartBorders (D a) F0) :
      A.dartBorders (D (f a)) F0 := by
    have hg := hforward (D a) ha
    obtain ⟨b, hb⟩ := himage (g (D a)) hg
    have hs := hattedSide_face_step_reflect hτ hfin (H := H) a b hb.symm
    change f a = b at hs
    rw [hs, hb]
    exact hg
  have hneg (a : ℕ × Bool) (ha : A.dartBorders (D a) F0) :
      A.dartBorders (D (f.symm a)) F0 := by
    have hg := hbackward (D a) ha
    obtain ⟨b, hb⟩ := himage (g.symm (D a)) hg
    have hstep : g (D b) = D a := by rw [hb, Equiv.apply_symm_apply]
    have hs := hattedSide_face_step_reflect hτ hfin (H := H) b a hstep
    change f b = a at hs
    have hs' : f.symm a = b := by rw [← hs, Equiv.symm_apply_apply]
    rw [hs', hb]
    exact hg
  have hd0 : A.dartBorders (D d) F0 := (hb (D d)).mpr hdF
  have hsucc : g (D d) = D (f d) := by
    obtain ⟨b, hb⟩ := himage (g (D d)) (hforward (D d) hd0)
    have hs := hattedSide_face_step_reflect hτ hfin (H := H) d b hb.symm
    exact hb.symm.trans (congrArg D hs.symm)
  have hiterpos (n : ℕ) : A.dartBorders (D ((f : _ → _)^[n] d)) F0 := by
    induction n with
    | zero => exact hd0
    | succ n ih => rw [Function.iterate_succ_apply']; exact hpos _ ih
  have hiterneg (n : ℕ) : A.dartBorders (D ((f.symm : _ → _)^[n] d)) F0 := by
    induction n with
    | zero => exact hd0
    | succ n ih => rw [Function.iterate_succ_apply']; exact hneg _ ih
  have hfinite : {a | f.SameCycle d a}.Finite := by
    have hraw : {r | A.dartBorders r F0}.Finite := by
      rw [hlist]
      exact (stageTriangleDartList w j0).finite_toSet
    apply (Set.Finite.preimage hinj.injOn hraw).subset
    intro a ha
    obtain ⟨i, rfl⟩ := ha
    cases i with
    | ofNat n =>
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq, Int.ofNat_eq_natCast,
        zpow_natCast, Equiv.Perm.coe_pow] using hiterpos n
    | negSucc n =>
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq, zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow,
        Equiv.Perm.inv_def] using hiterneg (n + 1)
  obtain ⟨j, hdj⟩ := finiteFaceOrbit_mem_triangle z
    (hatCodes_inducedFiniteIncidence _ hτ hfin) d hfinite
  obtain ⟨F', _, hborder', hretain⟩ :=
    boundaryGluing_nonneg_right_triangle_retained hτ hp P hqMode Tpath hfin hleft hk j
  have hFF : F' = F := hattedSide_border_face_unique G (hborder' d hdj) hdF
  exact ⟨⟨j, hdj, hretain.mpr (hFF ▸ hF)⟩, hsucc⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the exact retained-face predicates agree
under the hatted embedding, with the original ambient face successor. -/
theorem boundaryGluing_nonneg_right_retained_face_iff (d : ℕ × Bool) :
    (∃ j : TriangleCreationTime (hatCodes (boundaryGluingFutureStream W h k) hτ),
      d ∈ stageTriangleDartList (hatCodes (boundaryGluingFutureStream W h k) hτ) j ∧
      ∀ a ∈ stageTriangleDartList (hatCodes (boundaryGluingFutureStream W h k) hτ) j,
        a.1 ∈ (Q).edges) ↔
    (∃ F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (E d.1, d.2)) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp P .right) := by
  constructor
  · rintro ⟨j, hd, hall⟩
    obtain ⟨F, _, hborder, hretain⟩ := boundaryGluing_nonneg_right_triangle_retained
      hτ hp P hqMode Tpath hfin hleft hk j
    exact ⟨F, hborder d hd, hretain.mp hall⟩
  · intro hF
    exact (boundaryGluing_nonneg_right_retained_face_reflect
      hτ hp P hqMode Tpath hfin hleft hk d hF).1

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: retained face succession is preserved and
reflected on the hatted and actual right sides. -/
theorem boundaryGluing_nonneg_right_faceNext (d e : ℕ × Bool) :
    (Q).faceNext d e ↔ (S).faceNext (E d.1, d.2) (E e.1, e.2) := by
  let z := hatCodes (boundaryGluingFutureStream W h k) hτ
  let hz := hatCodes_inducedFiniteIncidence _ hτ hfin
  let D : (ℕ × Bool) → ℕ × Bool := fun a => (E a.1, a.2)
  have hinj : Function.Injective D := by
    intro a b hab
    have hb := congrArg (fun a : ℕ × Bool => a.2) hab
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ
      (congrArg Prod.fst hab)) hb
  have hc := boundaryGluing_decoded_stream W h k hτ
  have hcongr (a b : ℕ → Fin 3) (ha : KMSWFiniteIncidence a)
      (hb : KMSWFiniteIncidence b) (hab : a = b) :
      kmswInfFaceSucc a ha = kmswInfFaceSucc b hb := by subst b; rfl
  have hs := hcongr _ _ (sourceAncestor_finite_incidence
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime
    ⟨boundaryFutureHattedPath k W, hqMode⟩) hz hc
  have hpred : (∃ j : TriangleCreationTime
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))),
      d ∈ stageTriangleDartList _ j ∧ ∀ a ∈ stageTriangleDartList _ j, a.1 ∈ (Q).edges) ↔
      (∃ j : TriangleCreationTime z, d ∈ stageTriangleDartList z j ∧
        ∀ a ∈ stageTriangleDartList z j, a.1 ∈ (Q).edges) := by
    constructor
    · rintro ⟨j, hd, hall⟩
      let j' : TriangleCreationTime z := ⟨j.val, by dsimp only [z]; rw [← hc]; exact j.property⟩
      have hl : stageTriangleDartList _ j = stageTriangleDartList z j' := by
        simp only [stageTriangleDartList, stageTriangleDartTriple, j', hc, z]
      exact ⟨j', hl ▸ hd, hl ▸ hall⟩
    · rintro ⟨j, hd, hall⟩
      let j' : TriangleCreationTime
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) :=
        ⟨j.val, by rw [hc]; exact j.property⟩
      have hl : stageTriangleDartList _ j' = stageTriangleDartList z j := by
        simp only [stageTriangleDartList, stageTriangleDartTriple, j', hc, z]
      exact ⟨j', hl.symm ▸ hd, hl.symm ▸ hall⟩
  have hsd := congrArg (fun f : Equiv.Perm (ℕ × Bool) => f d) hs
  have hretain := boundaryGluing_nonneg_right_retained_face_iff
    hτ hp P hqMode Tpath hfin hleft hk d
  constructor
  · rintro ⟨htri, he⟩
    have hF := hretain.mp (hpred.mp htri)
    refine ⟨hF, ?_⟩
    have hm := (boundaryGluing_nonneg_right_retained_face_reflect
      hτ hp P hqMode Tpath hfin hleft hk d hF).2
    exact hm.trans (congrArg D (hsd.symm.trans he))
  · rintro ⟨hF, he⟩
    refine ⟨hpred.mpr (hretain.mpr hF), hsd.trans (hinj ?_)⟩
    exact (boundaryGluing_nonneg_right_retained_face_reflect
      hτ hp P hqMode Tpath hfin hleft hk d hF).2.symm.trans he

/-- Helper toward Lemma 5.5: the cell equivalence preserves the face tag. -/
theorem boundaryGluing_nonneg_right_faceNext_iff (u v : GeometricSideCell Q) :
    geometricSideRelation Q .faceNext u v ↔
      geometricSideRelation S .faceNext (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v with
    | inl a => rfl
    | inr e =>
      exact boundaryGluing_nonneg_right_faceNext
        hτ hp P hqMode Tpath hfin hleft hk d.val e.val

/-- Helper toward Lemma 5.5: the rightmost path from the source enumerates
the lower-right boundary with the same zero-based index. -/
private theorem hattedSide_rightmost_boundary (z : ℕ → Fin 3)
    (hf : KMSWFiniteIncidence z) (hL : ∀ n, 0 ≤ L z n)
    (ht : Filter.Tendsto (L z) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R z n ≤ a) (i : ℕ) :
    (kmswRightmostPath z hf hL ht hR 0).edge i = kmswRightBoundaryEdge z i := by
  induction i with
  | zero =>
    change kmswRightmostOutgoingEdge z hf hL ht hR
      (kmsw_vertex_allocated_of_finite_incidence z hf) 0 = _
    exact kmswRightmostOutgoingEdge_source z hf hL ht hR _
  | succ i ih =>
    have hv : kmswRightmostOrbit z hf hL ht hR 0 (i + 1) =
        edgeWest z (kmswRightBoundaryEdge z (i + 1)) := by
      rw [← (kmswRightmostPath_edge_spec z hf hL ht hR 0 i).2.2, ih]
      exact (kmswRightBoundary_infinite_path z hL hR).2.1 i
    change kmswRightmostOutgoingEdge z hf hL ht hR _
      (kmswRightmostOrbit z hf hL ht hR 0 (i + 1)) = _
    rw [hv]
    exact kmswRightBoundaryEdge_is_rightmost z hf hL ht hR (by omega)

/-- Helper toward Lemma 5.5: the hatted side's exterior marking starts
at edge zero and uses the lower-right record-edge index without a shift. -/
theorem boundaryGluing_nonneg_right_boundary_index (i : ℕ) :
    (Q).boundary i =
      (kmswRightBoundaryEdge
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i, false) := by
  exact congrArg (fun e : ℕ => (e, false)) (hattedSide_rightmost_boundary _
    (sourceAncestor_finite_incidence (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩)
    (sourceAncestor_left_nonneg (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩)
    (sourceAncestor_left_transient (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩)
    (sourceAncestor_right_unbounded (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩) i)

include hk in
/-- Helper toward Lemma 5.5: the index-zero exterior darts agree under
the hatted embedding, including at the endpoint k = 0. -/
theorem boundaryGluing_nonneg_right_boundary_zero :
    (E ((Q).boundary 0).1, ((Q).boundary 0).2) = (S).boundary 0 := by
  rw [boundaryGluing_nonneg_right_boundary_index hqMode 0,
    kmswRightBoundaryEdge_zero, boundaryGluingHatEdgeMap_zero]
  change (act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k), false) =
    (boundaryOuterEdge (shiftedStream W 0) h (k + (0 : ℕ)), false)
  rw [Nat.cast_zero, add_zero, boundaryGluing_active_eq_boundaryOuterEdge W h k hk]

/-- Helper toward Lemma 5.5: a right record attains the closed-prefix minimum. -/
private theorem hattedSide_record_min (w : ℕ → Fin 3) (m : ℕ)
    (hm : ∀ j < m, R w m < R w j) : minR w m = R w m := by
  obtain ⟨j, hj, he⟩ := runningMin_attained (R w) m
  have hle := runningMin_le (R w) m m le_rfl
  change minR w m ≤ R w m at hle
  change minR w m = R w j at he
  by_cases hjm : j < m
  · have := hm j hjm
    omega
  · have : j = m := by omega
    simpa only [this] using he

/-- Helper toward Lemma 5.5: the record count determines the vertical level,
including the record at time zero. -/
private theorem hattedSide_record_count (w : ℕ → Fin 3) (m : ℕ)
    (hm : ∀ j < m, R w m < R w j) :
    (Nat.count (fun n => ∀ j < n, R w n < R w j) m : ℤ) = -R w m := by
  classical
  have hlen := kmswStage_LR_length w m
  have hc : (kmswStage w m).LR.length =
      Nat.count (fun n => ∀ j < n, R w n < R w j) (m + 1) := by
    rw [kmswStage_LR_eq, List.length_map, length_filter_range]
    apply natCount_congr
    intro n _
    exact decide_eq_true_iff
  rw [hc, Nat.count_succ, ite_eq_left hm, Nat.cast_add, Nat.cast_one,
    hattedSide_record_min w m hm] at hlen
  omega

/-- Helper toward Lemma 5.5: the selected right record has level minus its
zero-based index. -/
private theorem hattedSide_selected_record (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (i : ℕ) :
    let m := natSelect (fun n => ∀ j < n, R w n < R w j) i
    (∀ j < m, R w m < R w j) ∧ R w m = -(i : ℤ) := by
  classical
  obtain ⟨hm, hc⟩ := natSelect_spec (right_record_infinite w hR) i
  have hv := hattedSide_record_count w _ hm
  rw [hc] at hv
  exact ⟨hm, by omega⟩

/-- Helper toward Lemma 5.5: a record at level minus i is exactly record i,
as an edge ID, independently of its endpoints. -/
private theorem hattedSide_record_edge (w : ℕ → Fin 3) (m i : ℕ)
    (hm : ∀ j < m, R w m < R w j) (hv : R w m = -(i : ℤ)) :
    act w m = kmswRightBoundaryEdge w i := by
  classical
  have hc := hattedSide_record_count w m hm
  have hc' : Nat.count (fun n => ∀ j < n, R w n < R w j) m = i := by omega
  unfold kmswRightBoundaryEdge
  rw [← hc', natSelect_count hm]

/-- Helper toward Lemma 5.5: the hatted vertical coordinate agrees with the
raw coordinate at the canonical R-stage time, including exit replacements. -/
theorem hattedSide_R_at_stageTime (w : ℕ → Fin 3) (hh : HasFlowLineHits w) :
    ∀ m, R (hatCodes w hh) m = R w (quadrantRStageTime w hh m) := by
  intro m
  induction m with
  | zero =>
    have ht : quadrantRStageTime w hh 0 = 0 :=
      quadrantRStageTime_eq_of_initial_R w hh (by
        have hp := (walkNL_spec w hh 0).1
        rw [walkNR_zero] at hp
        omega)
    simp only [ht, R, Finset.range_zero, Finset.sum_empty]
  | succ m ih =>
    have hs (u : ℕ → Fin 3) (n : ℕ) : R u (n + 1) =
        R u n + (lazyTwoDimensionalStep (u n)).2 := Finset.sum_range_succ _ _
    rw [hs, ih]
    by_cases hex : ∃ l, hatExitIndex w hh l = m
    · obtain ⟨l, rfl⟩ := hex
      have ht : quadrantRStageTime w hh (hatExitIndex w hh l + 1) =
          walkNR w hh (l + 1) := by
        rw [← hatCodeTime_succ, hatCodeTime_at_exit]
        have hp := (walkNR_succ_spec w hh l).1
        omega
      have hleft : R w (walkNL w hh l) = R w (walkNL w hh l - 1) := by
        have hi : walkNL w hh l - 1 + 1 = walkNL w hh l := by
          have hp := (walkNL_spec w hh l).1
          omega
        calc
          R w (walkNL w hh l) = R w (walkNL w hh l - 1 + 1) := congrArg (R w) hi.symm
          _ = R w (walkNL w hh l - 1) := by
            rw [hs, walkNL_previous_code w hh l]
            simp only [lazyTwoDimensionalStep, ↓reduceIte, add_zero]
      rw [quadrantRStageTime_hatExitIndex, ht, hatCodes_at_exit,
        (walkNR_succ_spec w hh l).2, hleft]
      rfl
    · have ht : quadrantRStageTime w hh (m + 1) = quadrantRStageTime w hh m + 1 := by
        rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w hh m hex]
      rw [ht, hs, hatCodes, hatCodeTime_of_not_exit w hh m hex]

/-- Helper toward Lemma 5.5: exact matching of the UR stacks also matches
the closed-prefix vertical minima at canonical R-stage times. -/
theorem hattedSide_minR_at_stageTime (w : ℕ → Fin 3) (hh : HasFlowLineHits w)
    (m : ℕ) : minR (hatCodes w hh) m = minR w (quadrantRStageTime w hh m) := by
  have hl := congrArg List.length (hatAll_sim w hh m).ur_eq
  rw [List.length_map] at hl
  have ha := kmswStage_UR_length (hatCodes w hh) m
  have hb := kmswStage_UR_length w (quadrantRStageTime w hh m)
  rw [hl, hattedSide_R_at_stageTime] at ha
  omega

/-- Helper toward Lemma 5.5: before the first downward level hit, the
vertical coordinate stays above its starting level. -/
private theorem hattedSide_R_floor (w : ℕ → Fin 3) (hh : HasFlowLineHits w)
    (a n : ℕ) (han : a ≤ n) (hn : n < firstFlowRHit w hh a) : R w a ≤ R w n := by
  have hstep (j : ℕ) : R w j - 1 ≤ R w (j + 1) := by
    have hs : R w (j + 1) = R w j + (lazyTwoDimensionalStep (w j)).2 :=
      Finset.sum_range_succ _ _
    have hb : (-1 : ℤ) ≤ (lazyTwoDimensionalStep (w j)).2 := by
      unfold lazyTwoDimensionalStep
      split_ifs <;> omega
    omega
  have hfloor : ∀ j, a ≤ j → j < firstFlowRHit w hh a → R w a ≤ R w j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hj ih =>
      intro hjlt
      have hp := ih (by omega)
      have hs := hstep j
      have hne : R w (j + 1) ≠ R w a - 1 := by
        intro he
        exact Nat.find_min (hh.2 a) hjlt ⟨by omega, he⟩
      omega
  exact hfloor n han hn

/-- Helper toward Lemma 5.5: each strict hatted right record is a strict
raw right record at its canonical creation time. -/
theorem hattedSide_record_at_stageTime (w : ℕ → Fin 3) (hh : HasFlowLineHits w)
    (m : ℕ) (hm : ∀ j < m, R (hatCodes w hh) m < R (hatCodes w hh) j) :
    ∀ j < quadrantRStageTime w hh m,
      R w (quadrantRStageTime w hh m) < R w j := by
  cases m with
  | zero =>
    have ht : quadrantRStageTime w hh 0 = 0 :=
      quadrantRStageTime_eq_of_initial_R w hh (by
        have hp := (walkNL_spec w hh 0).1
        rw [walkNR_zero] at hp
        omega)
    rw [ht]
    intro j hj
    omega
  | succ m =>
    have hlt : R w (quadrantRStageTime w hh (m + 1)) <
        minR w (quadrantRStageTime w hh m) := by
      obtain ⟨a, ha, he⟩ := runningMin_attained (R (hatCodes w hh)) m
      have hv := hm a (by omega)
      change minR (hatCodes w hh) m = R (hatCodes w hh) a at he
      rw [← he, hattedSide_minR_at_stageTime, hattedSide_R_at_stageTime] at hv
      exact hv
    intro j hj
    by_cases hjm : j ≤ quadrantRStageTime w hh m
    · exact hlt.trans_le (runningMin_le (R w) _ j hjm)
    · by_cases hex : ∃ l, hatExitIndex w hh l = m
      · obtain ⟨l, rfl⟩ := hex
        have ht : quadrantRStageTime w hh (hatExitIndex w hh l + 1) =
            walkNR w hh (l + 1) := by
          rw [← hatCodeTime_succ, hatCodeTime_at_exit]
          have hp := (walkNR_succ_spec w hh l).1
          omega
        rw [quadrantRStageTime_hatExitIndex] at hjm
        rw [ht] at hj ⊢
        have hf := hattedSide_R_floor w hh (walkNL w hh l) j (by omega)
          (show j < firstFlowRHit w hh (walkNL w hh l) from hj)
        rw [(walkNR_succ_spec w hh l).2]
        omega
      · have ht : quadrantRStageTime w hh (m + 1) = quadrantRStageTime w hh m + 1 := by
          rw [← hatCodeTime_succ, hatCodeTime_of_not_exit w hh m hex]
        rw [ht] at hj
        omega

/-- Helper toward Lemma 5.5: the hatted edge map preserves every indexed
right-boundary record edge, using active edge IDs at the aligned record times. -/
theorem hattedSide_hatLimitEdgeMap_rightBoundaryEdge (w : ℕ → Fin 3)
    (hh : HasFlowLineHits w) (i : ℕ) :
    hatLimitEdgeMap w hh (kmswRightBoundaryEdge (hatCodes w hh) i) =
      kmswRightBoundaryEdge w i := by
  classical
  let m := natSelect (fun n => ∀ j < n, R (hatCodes w hh) n < R (hatCodes w hh) j) i
  obtain ⟨hm, hv⟩ := hattedSide_selected_record (hatCodes w hh) (hat_R_unbounded_hatted w hh) i
  change hatLimitEdgeMap w hh (act (hatCodes w hh) m) = kmswRightBoundaryEdge w i
  rw [hatLimitEdgeMap_eq_stage w hh m _ (act_lt_nextEdge _ le_rfl)]
  have ha := (hatAll_sim w hh m).incidenceSim.active
  change hatAllEdgeMap w hh m (act (hatCodes w hh) m) = act w (quadrantRStageTime w hh m) at ha
  rw [ha]
  apply hattedSide_record_edge w _ i (hattedSide_record_at_stageTime w hh m hm)
  exact (hattedSide_R_at_stageTime w hh m).symm.trans hv

/-- Helper toward Lemma 5.5: vertical coordinates add under a raw future
shift, with the original absolute time retained. -/
private theorem hattedSide_R_shift_add (w : ℕ → Fin 3) (t n : ℕ) :
    R w (t + n) = R w t + R (fun j => w (t + j)) n := by
  induction n with
  | zero => simp only [R, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ n ih =>
    have hg : R w (t + n + 1) = R w (t + n) +
        (lazyTwoDimensionalStep (w (t + n))).2 := Finset.sum_range_succ _ _
    have hs : R (fun j => w (t + j)) (n + 1) =
        R (fun j => w (t + j)) n +
          (lazyTwoDimensionalStep (w (t + n))).2 := Finset.sum_range_succ _ _
    rw [Nat.add_succ, hg, hs, ih]
    omega

include hτ hk in
/-- Helper toward Lemma 5.5: the i-th future right record embeds as the
full stream's boundary edge at label k+i. This uses edge IDs and their
activation times, and includes the root at i=0. -/
theorem boundaryGluing_nonneg_future_rightBoundaryEdge (i : ℕ) :
    boundaryGluingEdgeMap W h k
      (kmswRightBoundaryEdge (boundaryGluingFutureStream W h k) i) =
      boundaryOuterEdge (shiftedStream W 0) h (k + (i : ℤ)) := by
  classical
  by_cases hi : i = 0
  · subst i
    rw [kmswRightBoundaryEdge_zero, Nat.cast_zero, add_zero]
    have hr : boundaryGluingEdgeMap W h k 0 =
        act (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) := by
      simpa only [boundaryGluingHatEdgeMap, Function.comp_apply, hatLimitEdgeMap_zero]
        using boundaryGluingHatEdgeMap_zero W h k hτ
    exact hr.trans (boundaryGluing_active_eq_boundaryOuterEdge W h k hk)
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let m := natSelect (fun n => ∀ j < n, R u n < R u j) i
  obtain ⟨hm, hv⟩ := hattedSide_selected_record u
    (R_unbounded_of_hasFlowLineHits u hτ) i
  have htval : R w t = -k := by
    by_cases hk0 : k = 0
    · simp only [t, hk0, boundaryHitTime_zero, R, Finset.range_zero,
        Finset.sum_empty, neg_zero]
    · exact boundaryHitTime_right_spec w h (by omega)
  have htmin : minR w t = R w t := by
    by_cases hk0 : k = 0
    · simp only [t, hk0, boundaryHitTime_zero, minR, runningMin]
    · exact ((kmswStage_UR_eq_nil_iff_record w t).mp
        (boundaryHit_right_UR_empty w h (by omega))).symm
  have hshift (n : ℕ) : R w (t + n) = R w t + R u n :=
    hattedSide_R_shift_add w t n
  have hval : R w (t + m) = -(k + (i : ℤ)) := by
    rw [hshift, htval, hv]
    omega
  have hrecord : ∀ j < t + m, R w (t + m) < R w j := by
    intro j hj
    by_cases hjt : j < t
    · have hb := runningMin_le (R w) t j hjt.le
      change minR w t ≤ R w j at hb
      rw [htmin, htval] at hb
      omega
    · have hlocal := hm (j - t) (by omega)
      have hs := hshift (j - t)
      rw [Nat.add_sub_of_le (by omega : t ≤ j)] at hs
      have hs' := hshift m
      omega
  have hki : 1 ≤ k + (i : ℤ) := by omega
  have hcast : ((k + (i : ℤ)).toNat : ℤ) = k + (i : ℤ) :=
    Int.toNat_of_nonneg (by omega)
  have he := hattedSide_record_edge w (t + m) (k + (i : ℤ)).toNat hrecord
    (by rw [hcast]; exact hval)
  rw [boundaryOuterEdge_of_positive _ h hki]
  change kmswWindowEdgeMapInf w t (act u m) = _
  rw [kmswWindowEdgeMapInf_eq_stage w t m _ (act_lt_nextEdge u le_rfl)]
  exact (kmswWindowPatchData_rel w t m).active.trans he

include hk in
/-- Helper toward Lemma 5.5: the decoded hatted right-boundary edge IDs
have exactly the original boundary labels k+i, with no index shift. -/
theorem boundaryGluing_nonneg_right_boundary_edge (i : ℕ) :
    E (kmswRightBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i) =
      boundaryOuterEdge (shiftedStream W 0) h (k + (i : ℤ)) := by
  rw [boundaryGluing_decoded_stream W h k hτ]
  change boundaryGluingEdgeMap W h k
    (hatLimitEdgeMap (boundaryGluingFutureStream W h k) hτ
      (kmswRightBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) i)) = _
  rw [hattedSide_hatLimitEdgeMap_rightBoundaryEdge]
  exact boundaryGluing_nonneg_future_rightBoundaryEdge hτ hk i

include hk in
/-- Helper toward Lemma 5.5: every indexed exterior boundary dart is
transported by the cell map, including the zero endpoint. -/
theorem boundaryGluing_nonneg_right_boundary (i : ℕ) :
    (E ((Q).boundary i).1, ((Q).boundary i).2) = (S).boundary i := by
  rw [boundaryGluing_nonneg_right_boundary_index hqMode i]
  exact congrArg (fun e : ℕ => (e, false))
    (boundaryGluing_nonneg_right_boundary_edge hτ hk i)

/-- Helper toward Lemma 5.5: the cell equivalence preserves each indexed
exterior boundary tag with the original edge IDs. -/
theorem boundaryGluing_nonneg_right_boundary_iff (i : ℕ) (u v : GeometricSideCell Q) :
    geometricSideRelation Q (.boundary i) u v ↔
      geometricSideRelation S (.boundary i) (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    change (Q).boundary i = d.val ↔ (S).boundary i = (E d.val.1, d.val.2)
    rw [← boundaryGluing_nonneg_right_boundary hτ hp P hqMode hk i]
    constructor
    · intro he
      exact congrArg (fun a : ℕ × Bool => (E a.1, a.2)) he
    · intro he
      have hs := congrArg (fun a : ℕ × Bool => a.2) he
      exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ
        (congrArg (fun a : ℕ × Bool => a.1) he))
        hs

include Tpath hfin hleft in
/-- Helper toward Lemma 5.5: the canonical hatted geodesic and the actual
cut geodesic have exactly the same indexed seam darts under the embedding. -/
theorem boundaryGluing_nonneg_right_seam (i : ℕ) :
    (E ((Q).seam i).1, ((Q).seam i).2) = (S).seam i := by
  exact congrArg (fun e : ℕ => (e, false))
    ((boundaryGluing_geodesicIdentification W h k hτ longest hqMode
      hp Tpath P hfin hleft i).symm)

/-- Helper toward Lemma 5.5: the cell equivalence preserves each indexed
geodesic seam tag. -/
theorem boundaryGluing_nonneg_right_seam_iff (i : ℕ) (u v : GeometricSideCell Q) :
    geometricSideRelation Q (.seam i) u v ↔
      geometricSideRelation S (.seam i) (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    change (Q).seam i = d.val ↔ (S).seam i = (E d.val.1, d.val.2)
    rw [← boundaryGluing_nonneg_right_seam hτ hp P hqMode Tpath hfin hleft i]
    constructor
    · intro he
      exact congrArg (fun a : ℕ × Bool => (E a.1, a.2)) he
    · intro he
      have hs := congrArg (fun a : ℕ × Bool => a.2) he
      exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ
        (congrArg (fun a : ℕ × Bool => a.1) he))
        hs

/-- Helper toward Lemma 5.5: the embedded hatted right side is isomorphic
to the actual nonnegative right side, preserving every geometric relation,
the root, the indexed exterior boundary and the indexed geodesic seam. -/
@[expose] noncomputable def boundaryGluing_nonneg_right_markedIso :
    GeometricSideMarkedIso Q S where
  equiv := Φ
  relation_iff := by
    intro t u v
    cases t with
    | vertex => exact boundaryGluing_nonneg_right_vertex_iff hτ hp P hqMode Tpath hfin hleft hk u v
    | root => exact boundaryGluing_nonneg_right_root_iff hτ hp P hqMode Tpath hfin hleft hk u v
    | incident => exact boundaryGluing_nonneg_right_incident_iff hτ hp P hqMode Tpath hfin hleft hk u v
    | opposite => exact boundaryGluing_nonneg_right_opposite_iff hτ hp P hqMode Tpath hfin hleft hk u v
    | oriented => exact boundaryGluing_nonneg_right_oriented_iff hτ hp P hqMode Tpath hfin hleft hk u v
    | rotation => exact boundaryGluing_nonneg_right_rotation_iff hτ hp P hqMode Tpath hfin hleft hk u v
    | faceNext => exact boundaryGluing_nonneg_right_faceNext_iff hτ hp P hqMode Tpath hfin hleft hk u v
    | target => exact boundaryGluing_nonneg_right_target_iff hτ hp P hqMode Tpath hfin hleft hk u v
    | boundary i => exact boundaryGluing_nonneg_right_boundary_iff hτ hp P hqMode Tpath hfin hleft hk i u v
    | seam i => exact boundaryGluing_nonneg_right_seam_iff hτ hp P hqMode Tpath hfin hleft hk i u v

include hτ Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the actual nonnegative right side admits the
complete marked isomorphism to its decoded hatted side. -/
theorem boundaryGluing_nonneg_right_markedIso_nonempty :
    Nonempty (GeometricSideMarkedIso S Q) := by
  let I := boundaryGluing_nonneg_right_markedIso hτ hp P hqMode Tpath hfin hleft hk
  refine ⟨⟨I.equiv.symm, ?_⟩⟩
  intro t u v
  simpa only [Equiv.apply_symm_apply] using
    (I.relation_iff t (I.equiv.symm u) (I.equiv.symm v)).symm

end DirectedDistances.PaperProofs.Section5
