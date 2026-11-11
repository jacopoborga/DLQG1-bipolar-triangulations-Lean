module

public import DirectedDistances.KMSW.InfiniteGeodesicAE
public import DirectedDistances.KMSW.CutSeparationAEPath
public import DirectedDistances.KMSW.CutSeparationAnyStart

/-! # Stabilized distances along UIQBOT records

Present edges retain their IDs. The compulsory-vertex argument implements -/

@[expose] public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory DirectedDistances.RandomWalk
open scoped Classical

private theorem vertex_id_ext {w : ℕ → Fin 3} {u v : PresentVertex w}
    (h : u.id = v.id) : u = v := by
  cases u
  cases v
  cases h
  rfl

private theorem endpoint_before {w : ℕ → Fin 3} {n : ℕ}
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {x z : PresentVertex w} (p : Path x z) (hx : x ∈ recordBefore w n)
    (havoid : recordVertex w n ∉ p.vertices) : z ∈ recordBefore w n := by
  induction p with
  | nil => exact hx
  | @cons y z p e ih =>
    have hy : y ∈ recordBefore w n := ih (by
      intro hmem
      exact havoid ((Path.mem_vertices_cons p e).2 (Or.inl hmem)))
    by_contra hz
    apply presentArrow_no_crossing w n hA hB e
    exact ⟨hy, hz, fun heq => havoid (heq ▸ (p.cons e).end_mem_vertices)⟩

/-- Every path from the old side to outside it visits the record vertex -/
theorem recordVertex_mem_path_from_before (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {x z : PresentVertex w} (hx : x ∈ recordBefore w n ∪ {recordVertex w n})
    (hz : z ∉ recordBefore w n) (p : Path x z) :
    recordVertex w n ∈ p.vertices := by
  rcases hx with hx | hx
  · by_contra havoid
    exact hz (endpoint_before hA hB p hx havoid)
  · subst x
    exact p.start_mem_vertices

/-- SDP splits at a record, including unreachable endpoints -/
theorem sdp_eq_add_recordVertex (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {x z : PresentVertex w} (hx : x ∈ recordBefore w n ∪ {recordVertex w n})
    (hz : z ∉ recordBefore w n) :
    sdp x z = sdp x (recordVertex w n) + sdp (recordVertex w n) z :=
  sdp_eq_add_of_forall_mem_vertices (recordVertex_mem_path_from_before w n hA hB hx hz)

/-- Longest distance in the present-edge quiver. Bottom means unreachable;
unbounded lengths give top inside `ℕ∞`. Finite values are established by
actual maximizing paths before any integer subtraction -/
noncomputable def presentLdp {w : ℕ → Fin 3} (x z : PresentVertex w) : WithBot ℕ∞ :=
  ⨆ p : Path x z, ((p.length : ℕ∞) : WithBot ℕ∞)

/-- An actual longest path identifies the extended distance with a finite value -/
theorem presentLdp_eq_length {w : ℕ → Fin 3} {x z : PresentVertex w}
    {p : Path x z} (hp : IsLongest p) :
    presentLdp x z = ((p.length : ℕ∞) : WithBot ℕ∞) := by
  apply le_antisymm
  · apply iSup_le
    intro q
    exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (hp q))
  · exact le_iSup (fun q : Path x z => ((q.length : ℕ∞) : WithBot ℕ∞)) p

private theorem presentLdp_eq_bot {w : ℕ → Fin 3} {x z : PresentVertex w}
    (h : ¬ Reachable x z) : presentLdp x z = ⊥ := by
  let : IsEmpty (Path x z) := ⟨fun p => h ⟨p⟩⟩
  exact iSup_of_empty _

private theorem presentLdp_eq_coe_iSup {w : ℕ → Fin 3} {x z : PresentVertex w}
    (h : Reachable x z) :
    presentLdp x z = (↑(⨆ p : Path x z, (p.length : ℕ∞)) : WithBot ℕ∞) := by
  let : Nonempty (Path x z) := h
  exact (WithBot.coe_iSup (f := fun p : Path x z => (p.length : ℕ∞))
    (OrderTop.bddAbove _)).symm

/-- LDP splits at a compulsory record vertex. Bottom is preserved for
unreachable pairs; the assertion also holds before boundedness is proved -/
theorem presentLdp_eq_add_recordVertex (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {x z : PresentVertex w} (hx : x ∈ recordBefore w n ∪ {recordVertex w n})
    (hz : z ∉ recordBefore w n) :
    presentLdp x z = presentLdp x (recordVertex w n) + presentLdp (recordVertex w n) z := by
  have hsep := recordVertex_mem_path_from_before w n hA hB hx hz
  by_cases hxy : Reachable x (recordVertex w n)
  · by_cases hyz : Reachable (recordVertex w n) z
    · have hxz : Reachable x z := by
        obtain ⟨p⟩ := hxy
        obtain ⟨q⟩ := hyz
        exact ⟨p.comp q⟩
      let : Nonempty (Path x (recordVertex w n)) := hxy
      let : Nonempty (Path (recordVertex w n) z) := hyz
      rw [presentLdp_eq_coe_iSup hxz, presentLdp_eq_coe_iSup hxy,
        presentLdp_eq_coe_iSup hyz, ← WithBot.coe_add]
      apply congrArg (fun a : ℕ∞ => (a : WithBot ℕ∞))
      apply le_antisymm
      · apply iSup_le
        intro r
        obtain ⟨p, q, rfl⟩ := r.exists_eq_comp_of_mem_vertices (hsep r)
        rw [Path.length_comp, ENat.natCast_add]
        exact add_le_add (le_iSup (fun p : Path x (recordVertex w n) => (p.length : ℕ∞)) p)
          (le_iSup (fun q : Path (recordVertex w n) z => (q.length : ℕ∞)) q)
      · apply ENat.iSup_add_iSup_le
        intro p q
        have h := le_iSup (fun r : Path x z => (r.length : ℕ∞)) (p.comp q)
        simpa only [Path.length_comp, ENat.natCast_add] using h
    · have hxz : ¬ Reachable x z := by
        rintro ⟨r⟩
        obtain ⟨p, q, _⟩ := r.exists_eq_comp_of_mem_vertices (hsep r)
        exact hyz ⟨q⟩
      rw [presentLdp_eq_bot hyz, presentLdp_eq_bot hxz, WithBot.add_bot]
  · have hxz : ¬ Reachable x z := by
      rintro ⟨r⟩
      obtain ⟨p, q, _⟩ := r.exists_eq_comp_of_mem_vertices (hsep r)
      exact hxy ⟨p⟩
    rw [presentLdp_eq_bot hxy, presentLdp_eq_bot hxz, WithBot.bot_add]

/-- The right-boundary vertices with the source at index zero and the east
endpoint of `r_k` at index `k+1` (`eqn-busemann-vertex`, -/
noncomputable def rightBoundaryVertex (w : ℕ → Fin 3) : ℕ → PresentVertex w
  | 0 => ⟨0⟩
  | k + 1 => ⟨edgeEast w (kmswRightBoundaryEdge w k)⟩

private theorem boundary_eq_record (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (k : ℕ) :
    rightBoundaryVertex w k = recordVertex w
      (natSelect (fun m => ∀ j, j < m → R w m < R w j) k) := by
  have hpath := kmswRightBoundary_infinite_path w hL hR
  have he : (rightBoundaryVertex w k).id = edgeWest w (kmswRightBoundaryEdge w k) := by
    cases k with
    | zero => exact hpath.2.2.1.symm
    | succ k => exact hpath.2.1 k
  apply vertex_id_ext
  rw [he]
  exact (edge_endpoints_eq w (act_lt_nextEdge w (le_refl _))).1.symm

private def extremal {w : ℕ → Fin 3} (longest : Bool) {x z : PresentVertex w}
    (p : Path x z) : Prop := if longest then IsLongest p else IsShortest p

private theorem extremal_length_eq {w : ℕ → Fin 3} {longest : Bool}
    {x z : PresentVertex w} {p q : Path x z}
    (hp : extremal longest p) (hq : extremal longest q) : p.length = q.length := by
  cases longest
  · exact Nat.le_antisymm (hp q) (hq p)
  · exact Nat.le_antisymm (hq p) (hp q)

private theorem extremal_comp_left {w : ℕ → Fin 3} {longest : Bool}
    {x y z : PresentVertex w} {p : Path x y} {q : Path y z}
    (hp : extremal longest (p.comp q)) : extremal longest p := by
  cases longest
  · exact IsShortest.of_comp_left hp
  · exact IsLongest.of_comp_left hp

private theorem extremal_comp_right {w : ℕ → Fin 3} {longest : Bool}
    {x y z : PresentVertex w} {p : Path x y} {q : Path y z}
    (hp : extremal longest (p.comp q)) : extremal longest q := by
  cases longest
  · exact IsShortest.of_comp_right hp
  · exact IsLongest.of_comp_right hp

private theorem extremal_difference {w : ℕ → Fin 3} {longest : Bool}
    {x x' y z : PresentVertex w}
    {p : Path x y} {q : Path x' y} {r : Path x z} {s : Path x' z}
    (hp : extremal longest p) (hq : extremal longest q)
    (hr : extremal longest r) (hs : extremal longest s)
    (hyr : y ∈ r.vertices) (hys : y ∈ s.vertices) :
    (r.length : ℤ) - (s.length : ℤ) = (p.length : ℤ) - (q.length : ℤ) := by
  obtain ⟨r₁, r₂, rfl⟩ := r.exists_eq_comp_of_mem_vertices hyr
  obtain ⟨s₁, s₂, rfl⟩ := s.exists_eq_comp_of_mem_vertices hys
  have hp' := extremal_length_eq (extremal_comp_left hr) hp
  have hq' := extremal_length_eq (extremal_comp_left hs) hq
  have ht := extremal_length_eq (extremal_comp_right hr) (extremal_comp_right hs)
  rw [Path.length_comp, Path.length_comp, hp', hq', ht, Int.natCast_add,
    Int.natCast_add, add_sub_add_right_eq_sub]

/-- An integer difference represented by actual maximizing (or minimizing)
paths to a record. This relation never subtracts infinite distances -/
def RecordDistanceDifference (w : ℕ → Fin 3) (longest : Bool) (k t : ℕ) (v : ℤ) : Prop :=
  ∃ p : Path (rightBoundaryVertex w k) (recordVertex w t),
    ∃ q : Path (rightBoundaryVertex w 0) (recordVertex w t),
      (if longest then IsLongest p ∧ IsLongest q else IsShortest p ∧ IsShortest q) ∧
      (p.length : ℤ) - (q.length : ℤ) = v

private theorem difference_unique {w : ℕ → Fin 3} {longest : Bool} {k t : ℕ}
    {u v : ℤ} (hu : RecordDistanceDifference w longest k t u)
    (hv : RecordDistanceDifference w longest k t v) : u = v := by
  obtain ⟨p, q, hpq, hu⟩ := hu
  obtain ⟨r, s, hrs, hv⟩ := hv
  have hp : extremal longest p := by cases longest <;> exact hpq.1
  have hq : extremal longest q := by cases longest <;> exact hpq.2
  have hr : extremal longest r := by cases longest <;> exact hrs.1
  have hs : extremal longest s := by cases longest <;> exact hrs.2
  rw [← hu, ← hv, extremal_length_eq hp hr, extremal_length_eq hq hs]

private theorem sequence_R_unbounded (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n) (hnzero : n 0 = 0)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1) :
    ∀ a : ℤ, ∃ t, R w t ≤ a := by
  have hbound : ∀ k, R w (n k) ≤ -(k : ℤ) := by
    intro k
    induction k with
    | zero => simp only [hnzero, R, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
        neg_zero, le_refl]
    | succ k ih =>
      have h := hA (k + 1) (n k) (hn (by omega))
      rw [Nat.cast_add, Nat.cast_one]
      omega
  intro a
  refine ⟨n ((-a).natAbs), ?_⟩
  have ha := Int.le_natAbs (a := -a)
  have hb := hbound ((-a).natAbs)
  omega

/-- A sequence beginning at zero gives horizontal nonnegativity from its first -/
theorem recordSequence_L_nonneg (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hnzero : n 0 = 0) (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j) :
    ∀ j, 0 ≤ L w j := by
  intro j
  have h := hB 0 j (by omega)
  simpa only [hnzero, L, Finset.range_zero, Finset.sum_empty] using h

private theorem record_difference_exists (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ t, R w t ≤ a)
    (longest : Bool) (k t : ℕ)
    (hAt : ∀ j < t, R w t ≤ R w j - 1)
    (hBt : ∀ j, t ≤ j → L w t ≤ L w j)
    (hkt : natSelect (fun m => ∀ j, j < m → R w m < R w j) k < t) (ht : 0 < t) :
    ∃ v, RecordDistanceDifference w longest k t v := by
  let a := natSelect (fun m => ∀ j, j < m → R w m < R w j) k
  have hAa : ∀ j < a, R w a ≤ R w j - 1 := by
    intro j hj
    have hh := (natSelect_spec (right_record_infinite w hR) k).1 j hj
    change R w a < R w j at hh
    omega
  have he := recordVertex_exists_extremal w hkt hAa hAt hBt
  have he0 := recordVertex_exists_extremal w ht (by intro j hj; omega) hAt hBt
  rw [← boundary_eq_record w hL hR k] at he
  change (∃ p : Path (rightBoundaryVertex w 0) (recordVertex w t), IsLongest p) ∧
    (∃ p : Path (rightBoundaryVertex w 0) (recordVertex w t), IsShortest p) at he0
  cases longest
  · obtain ⟨p, hp⟩ := he.2
    obtain ⟨q, hq⟩ := he0.2
    exact ⟨_, p, q, ⟨hp, hq⟩, rfl⟩
  · obtain ⟨p, hp⟩ := he.1
    obtain ⟨q, hq⟩ := he0.1
    exact ⟨_, p, q, ⟨hp, hq⟩, rfl⟩

private theorem difference_stable (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ t, R w t ≤ a)
    (longest : Bool) (k b c : ℕ)
    (hkb : natSelect (fun m => ∀ j, j < m → R w m < R w j) k < b)
    (hb : 0 < b) (hbc : b ≤ c)
    (hAb : ∀ j < b, R w b ≤ R w j - 1)
    (hBb : ∀ j, b ≤ j → L w b ≤ L w j)
    (hAc : ∀ j < c, R w c ≤ R w j - 1)
    {u v : ℤ} (hu : RecordDistanceDifference w longest k b u)
    (hv : RecordDistanceDifference w longest k c v) : v = u := by
  by_cases heq : b = c
  · subst c
    exact difference_unique hv hu
  have hbc' : b < c := by omega
  obtain ⟨p, q, hpq, hu⟩ := hu
  obtain ⟨r, s, hrs, hv⟩ := hv
  have hp : extremal longest p := by cases longest <;> exact hpq.1
  have hq : extremal longest q := by cases longest <;> exact hpq.2
  have hr : extremal longest r := by cases longest <;> exact hrs.1
  have hs : extremal longest s := by cases longest <;> exact hrs.2
  have hyr : recordVertex w b ∈ r.vertices := by
    have hsep : ∀ r : Path (rightBoundaryVertex w k) (recordVertex w c),
        recordVertex w b ∈ r.vertices := by
      rw [boundary_eq_record w hL hR k]
      intro r
      exact recordVertex_mem_path w hkb hbc' hAb hBb hAc r
    exact hsep r
  have hys : recordVertex w b ∈ s.vertices :=
    recordVertex_mem_path w hb hbc' hAb hBb hAc s
  exact hv.symm.trans ((extremal_difference hp hq hr hs hyr hys).trans hu)

/-- Existence and uniqueness of the eventual finite extremal-distance difference,
with the quantifier over all sufficiently late times satisfying the literal
record barriers. This is the definition gate; no choice of a Busemann value
precedes this theorem (`eqn-busemann-vertex`, -/
theorem existsUnique_eventual_recordDifference (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j)
    (hS : {t : ℕ | (∀ j < t, R w t ≤ R w j - 1) ∧
      ∀ j, t ≤ j → L w t ≤ L w j}.Infinite)
    (longest : Bool) (k : ℕ) :
    ∃! v : ℤ, ∃ N : ℕ, ∀ t, N ≤ t →
      (∀ j < t, R w t ≤ R w j - 1) →
      (∀ j, t ≤ j → L w t ≤ L w j) →
      RecordDistanceDifference w longest k t v := by
  obtain ⟨n, hn, hnzero, hnr⟩ := infinite_natSet_exists_enumeration_zero _ hS
    (zero_mem_records_of_L_nonneg w hL)
  have hrec (i : ℕ) : (∀ j < n i, R w (n i) ≤ R w j - 1) ∧
      ∀ j, n i ≤ j → L w (n i) ≤ L w j := by
    have hm : n i ∈ Set.range n := ⟨i, rfl⟩
    rw [hnr] at hm
    exact hm
  have hR := sequence_R_unbounded w n hn hnzero (fun i => (hrec i).1)
  let a := natSelect (fun m => ∀ j, j < m → R w m < R w j) k
  obtain ⟨b, hbrec, hab⟩ := hS.exists_gt a
  have hb : 0 < b := by omega
  obtain ⟨v, hv⟩ := record_difference_exists w hL hR longest k b hbrec.1 hbrec.2 hab hb
  refine ⟨v, ⟨b, ?_⟩, ?_⟩
  · intro t hbt hAt hBt
    obtain ⟨u, hu⟩ := record_difference_exists w hL hR longest k t hAt hBt
      (hab.trans_le hbt) (hb.trans_le hbt)
    have heq := difference_stable w hL hR longest k b t hab hb hbt hbrec.1 hbrec.2 hAt hv hu
    exact heq ▸ hu
  · rintro u ⟨N, hN⟩
    obtain ⟨t, htrec, ht⟩ := hS.exists_gt (max N b)
    have hu := hN t (by omega) htrec.1 htrec.2
    have htv := record_difference_exists w hL hR longest k t htrec.1 htrec.2
      (by omega) (by omega)
    obtain ⟨v', hv'⟩ := htv
    have hstable := difference_stable w hL hR longest k b t hab hb (by omega)
      hbrec.1 hbrec.2 htrec.1 hv hv'
    exact (difference_unique hu hv').trans hstable

private theorem record_mem_before (w : ℕ → Fin 3) {a b : ℕ} (hab : a < b)
    (hAb : ∀ j < b, R w b ≤ R w j - 1) : recordVertex w a ∈ recordBefore w b := by
  have hbound := (kmswStage_endpoints_lt_nextVertex w b (act w a)
    (act_lt_nextEdge w hab.le)).1
  have hends := (edge_endpoints_eq w (act_lt_nextEdge w hab.le)).1
  rw [hends, ← (edge_endpoints_eq w (act_lt_nextEdge w (le_refl a))).1] at hbound
  refine ⟨hbound, ?_, ?_⟩
  · intro heq
    exact recordVertex_ne w hab hAb (vertex_id_ext heq)
  · intro heq
    apply activeEast_ne_activeInitial w hab.le
    rw [CutConverse.activeInitial_eq]
    exact heq.symm

private theorem region_finite (w : ℕ → Fin 3) (n : ℕ) :
    (recordBefore w n ∪ {recordVertex w n}).Finite := by
  apply Set.Finite.union _ (Set.finite_singleton _)
  apply Set.Finite.subset (Set.finite_range
    (fun i : Fin (kmswStage w n).nextVertex => (⟨i.val⟩ : PresentVertex w)))
  intro u hu
  exact ⟨⟨u.id, hu.1⟩, vertex_id_ext rfl⟩

private def boundaryChainPath (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (he : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) :
    (N : ℕ) → Path (⟨edgeWest w (e 0)⟩ : PresentVertex w) ⟨edgeWest w (e N)⟩
  | 0 => .nil
  | N + 1 => (boundaryChainPath w e hp he N).cons ⟨e N, hp N, rfl, he N⟩

private theorem boundaryChainPath_length (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (he : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) (N : ℕ) :
    (boundaryChainPath w e hp he N).length = N := by
  induction N with
  | zero => rfl
  | succ N ih => exact congrArg Nat.succ ih

private theorem mem_vertices_comp_left {w : ℕ → Fin 3} {x y z : PresentVertex w}
    (p : Path x y) (q : Path y z) {u : PresentVertex w} (hu : u ∈ p.vertices) :
    u ∈ (p.comp q).vertices := by
  induction q with
  | nil => exact hu
  | cons q e ih => exact (Path.mem_vertices_cons (p.comp q) e).2 (Or.inl ih)

private theorem before_reaches_record (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ t, R w t ≤ a) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (x : PresentVertex w) (hx : x ∈ recordBefore w n) : Reachable x (recordVertex w n) := by
  obtain ⟨e, _, he, hstart, hp⟩ := allocated_vertex_has_infinite_path_of_R_unbounded
    w hR x.id ⟨n, hx.1⟩
  have hp' : ∀ i, EdgePresent w (e i) := fun i => hp i
  have hsource : (⟨edgeWest w (e 0)⟩ : PresentVertex w) = x := vertex_id_ext hstart
  have hx' : (⟨edgeWest w (e 0)⟩ : PresentVertex w) ∈ recordBefore w n := hsource.symm ▸ hx
  have hfin := region_finite w n
  let N := hfin.toFinset.card + 1
  let p := boundaryChainPath w e hp' he N
  have hvisit : recordVertex w n ∈ p.vertices := by
    by_contra havoid
    have hc : ∀ z ∈ p.vertices, z ∈ recordBefore w n ∪ {recordVertex w n} := by
      intro z hz
      obtain ⟨p₁, p₂, hpq⟩ := p.exists_eq_comp_of_mem_vertices hz
      left
      apply endpoint_before hA hB p₁ hx'
      intro hv
      apply havoid
      rw [hpq]
      exact mem_vertices_comp_left p₁ p₂ hv
    have hsub : p.vertices.toFinset ⊆ hfin.toFinset := by
      intro z hz
      exact hfin.mem_toFinset.2 (hc z (List.mem_toFinset.1 hz))
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup (vertices_nodup_of_acyclic (presentVertex_acyclic w) p),
      Path.vertices_length] at hcard
    have hlen : p.length = N := boundaryChainPath_length w e hp' he N
    dsimp only [N] at hlen
    omega
  obtain ⟨p₁, _, _⟩ := p.exists_eq_comp_of_mem_vertices hvisit
  exact hsource ▸ (show Reachable (⟨edgeWest w (e 0)⟩ : PresentVertex w)
    (recordVertex w n) from ⟨p₁⟩)

private theorem path_end_allocated {w : ℕ → Fin 3} {x z : PresentVertex w}
    (p : Path x z) (hx : ∃ t, x.id < (kmswStage w t).nextVertex) :
    ∃ t, z.id < (kmswStage w t).nextVertex := by
  cases p with
  | nil => exact hx
  | @cons y z p e =>
    obtain ⟨t, ht, _⟩ := e.property.1
    have hends := edge_endpoints_eq w ht
    refine ⟨t, ?_⟩
    rw [← e.property.2.2, ← hends.2]
    exact (kmswStage_endpoints_lt_nextVertex w t e.val ht).2

/-- Every allocated start has finitely many actual arrow-valued paths to any
fixed endpoint, when the qualifying records increase from zero. Extending to
a later record reduces this to the proved finite record-path family; parallel -/
theorem recordSequence_paths_finite (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n) (hnzero : n 0 = 0)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (x z : PresentVertex w) (hx : ∃ t, x.id < (kmswStage w t).nextVertex) :
    Finite (Path x z) := by
  by_cases hr : Reachable x z
  · obtain ⟨p⟩ := hr
    have hz := path_end_allocated p hx
    have hR := sequence_R_unbounded w n hn hnzero hA
    obtain ⟨a, ha⟩ := allocated_vertex_eventually_activeInitial_of_R_unbounded w hR x.id hx
    obtain ⟨b, hb⟩ := allocated_vertex_eventually_activeInitial_of_R_unbounded w hR z.id hz
    have hxa : recordVertex w a = x := vertex_id_ext (by
      simpa only [CutConverse.activeInitial_eq, recordVertex] using ha)
    have hzb : recordVertex w b = z := vertex_id_ext (by
      simpa only [CutConverse.activeInitial_eq, recordVertex] using hb)
    let M := max a b + 1
    have hM : M ≤ n M := by
      have := hn.add_le_nat M 0
      simpa only [hnzero, Nat.add_zero] using this
    have hac : a < n M := by dsimp only [M] at *; omega
    have hbc : b < n M := by dsimp only [M] at *; omega
    have hzbefore : z ∈ recordBefore w (n M) := hzb ▸ record_mem_before w hbc (hA M)
    obtain ⟨q⟩ := before_reaches_record w hR (n M) (hA M) (hB M) z hzbefore
    have hf : Finite (Path x (recordVertex w (n M))) := by
      rw [← hxa]
      exact recordVertex_paths_finite w hac (hA M) (hB M)
    let := hf
    exact Finite.of_injective (fun p : Path x z => p.comp q) q.comp_injective_left
  · let : IsEmpty (Path x z) := ⟨fun p => hr ⟨p⟩⟩
    infer_instance

/-- Record splitting together with actual path finiteness on the prescribed
record-sequence domain. Endpoints outside the old side include every vertex
in the new part; unreachable pairs retain bottom LDP and top SDP -/
theorem recordSequence_splitting (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n) (hnzero : n 0 = 0)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (m : ℕ) {x z : PresentVertex w}
    (hx : x ∈ recordBefore w (n m) ∪ {recordVertex w (n m)})
    (hz : z ∉ recordBefore w (n m)) :
    Finite (Path x z) ∧
      (∀ p : Path x z, recordVertex w (n m) ∈ p.vertices) ∧
      presentLdp x z = presentLdp x (recordVertex w (n m)) +
        presentLdp (recordVertex w (n m)) z ∧
      sdp x z = sdp x (recordVertex w (n m)) + sdp (recordVertex w (n m)) z := by
  have hxalloc : ∃ t, x.id < (kmswStage w t).nextVertex := by
    rcases hx with hx | hx
    · exact ⟨n m, hx.1⟩
    · subst x
      exact ⟨n m, (kmswStage_endpoints_lt_nextVertex w (n m) (act w (n m))
        (act_lt_nextEdge w le_rfl)).1⟩
  exact ⟨recordSequence_paths_finite w n hn hnzero hA hB x z hxalloc,
    recordVertex_mem_path_from_before w (n m) (hA m) (hB m) hx hz,
    presentLdp_eq_add_recordVertex w (n m) (hA m) (hB m) hx hz,
    sdp_eq_add_recordVertex w (n m) (hA m) (hB m) hx hz⟩

/-- All reachable allocated pairs have attained finite longest and shortest
lengths. Finiteness counts actual paths, including parallel arrows -/
theorem recordSequence_exists_extremal (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n) (hnzero : n 0 = 0)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (x z : PresentVertex w) (hx : ∃ t, x.id < (kmswStage w t).nextVertex)
    (hr : Reachable x z) :
    (∃ p : Path x z, IsLongest p) ∧ (∃ p : Path x z, IsShortest p) := by
  let : Finite (Path x z) := recordSequence_paths_finite w n hn hnzero hA hB x z hx
  have hfin : (pathLengths x z).Finite := Set.finite_range (fun p : Path x z => p.length)
  exact ⟨exists_isLongest_of_bddAbove hfin.bddAbove hr, exists_isShortest hr⟩

private theorem rightBoundary_edgePresent (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ t, R w t ≤ a) (i : ℕ) :
    EdgePresent w (kmswRightBoundaryEdge w i) := by
  obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually w hR i
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp (hN N le_rfl)
  have hmem : kmswRightBoundaryEdge w i ∈ (kmswStage w N).LR :=
    hv ▸ List.getElem_mem hi
  exact ⟨N, (kmswStage_boundary_ids_lt_nextEdge w N).2 _
    (List.mem_append_right _ hmem), (kmswStage_status w N).2.2.1 _ hmem⟩

/-- The actual right-boundary path joins the source to each `x_k` by present -/
theorem rightBoundaryVertex_reachable (w : ℕ → Fin 3)
    (hL : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ t, R w t ≤ a) (k : ℕ) :
    Reachable (rightBoundaryVertex w 0) (rightBoundaryVertex w k) := by
  have hpath := kmswRightBoundary_infinite_path w hL hR
  have hzero : (⟨edgeWest w (kmswRightBoundaryEdge w 0)⟩ : PresentVertex w) =
      rightBoundaryVertex w 0 := vertex_id_ext hpath.2.2.1
  have hk : (⟨edgeWest w (kmswRightBoundaryEdge w k)⟩ : PresentVertex w) =
      rightBoundaryVertex w k := by
    cases k with
    | zero => exact hzero
    | succ k => exact vertex_id_ext (hpath.2.1 k).symm
  rw [← hzero, ← hk]
  exact ⟨boundaryChainPath w (kmswRightBoundaryEdge w)
    (rightBoundary_edgePresent w hR) hpath.2.1 k⟩

/-- The LDP Busemann value, selected only after existence and uniqueness of its
intrinsic eventual characterization have been proved -/
noncomputable def busemannUIQBOT_LDP (w : ℕ → Fin 3) (k : ℕ)
    (hL : ∀ j, 0 ≤ L w j)
    (hS : {t : ℕ | (∀ j < t, R w t ≤ R w j - 1) ∧
      ∀ j, t ≤ j → L w t ≤ L w j}.Infinite) : ℤ :=
  (existsUnique_eventual_recordDifference w hL hS true k).choose

/-- The SDP counterpart, with the same existence-before-choice gate -/
noncomputable def busemannUIQBOT_SDP (w : ℕ → Fin 3) (k : ℕ)
    (hL : ∀ j, 0 ≤ L w j)
    (hS : {t : ℕ | (∀ j < t, R w t ≤ R w j - 1) ∧
      ∀ j, t ≤ j → L w t ≤ L w j}.Infinite) : ℤ :=
  (existsUnique_eventual_recordDifference w hL hS false k).choose

/-- Intrinsic eventual characterization of the chosen LDP value -/
theorem busemannUIQBOT_LDP_spec (w : ℕ → Fin 3) (k : ℕ)
    (hL : ∀ j, 0 ≤ L w j)
    (hS : {t : ℕ | (∀ j < t, R w t ≤ R w j - 1) ∧
      ∀ j, t ≤ j → L w t ≤ L w j}.Infinite) :
    ∃ N : ℕ, ∀ t, N ≤ t →
      (∀ j < t, R w t ≤ R w j - 1) →
      (∀ j, t ≤ j → L w t ≤ L w j) →
      RecordDistanceDifference w true k t (busemannUIQBOT_LDP w k hL hS) :=
  (existsUnique_eventual_recordDifference w hL hS true k).choose_spec.1

/-- Intrinsic eventual characterization of the chosen SDP value -/
theorem busemannUIQBOT_SDP_spec (w : ℕ → Fin 3) (k : ℕ)
    (hL : ∀ j, 0 ≤ L w j)
    (hS : {t : ℕ | (∀ j < t, R w t ≤ R w j - 1) ∧
      ∀ j, t ≤ j → L w t ≤ L w j}.Infinite) :
    ∃ N : ℕ, ∀ t, N ≤ t →
      (∀ j < t, R w t ≤ R w j - 1) →
      (∀ j, t ≤ j → L w t ≤ L w j) →
      RecordDistanceDifference w false k t (busemannUIQBOT_SDP w k hL hS) :=
  (existsUnique_eventual_recordDifference w hL hS false k).choose_spec.1

/-- The difference relation for LDP gives literal finite distance values, with
no conversion of an infinite distance to an integer -/
theorem RecordDistanceDifference.ldp_values {w : ℕ → Fin 3} {k t : ℕ} {v : ℤ}
    (h : RecordDistanceDifference w true k t v) :
    ∃ a b : ℕ,
      presentLdp (rightBoundaryVertex w k) (recordVertex w t) = ((a : ℕ∞) : WithBot ℕ∞) ∧
      presentLdp (rightBoundaryVertex w 0) (recordVertex w t) = ((b : ℕ∞) : WithBot ℕ∞) ∧
      (a : ℤ) - (b : ℤ) = v := by
  obtain ⟨p, q, hpq, hv⟩ := h
  exact ⟨p.length, q.length, presentLdp_eq_length hpq.1, presentLdp_eq_length hpq.2, hv⟩

/-- The analogous finite-value statement for SDP -/
theorem RecordDistanceDifference.sdp_values {w : ℕ → Fin 3} {k t : ℕ} {v : ℤ}
    (h : RecordDistanceDifference w false k t v) :
    ∃ a b : ℕ,
      sdp (rightBoundaryVertex w k) (recordVertex w t) = a ∧
      sdp (rightBoundaryVertex w 0) (recordVertex w t) = b ∧
      (a : ℤ) - (b : ℤ) = v := by
  obtain ⟨p, q, hpq, hv⟩ := h
  exact ⟨p.length, q.length, ((isShortest_iff_length_eq_sdp p).1 hpq.1).symm,
    ((isShortest_iff_length_eq_sdp q).1 hpq.2).symm, hv⟩

/-- Any strictly increasing sequence of qualifying records supplies infinitely -/
theorem recordSequence_records_infinite (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j) :
    {t : ℕ | (∀ j < t, R w t ≤ R w j - 1) ∧
      ∀ j, t ≤ j → L w t ≤ L w j}.Infinite := by
  apply (Set.infinite_range_of_injective hn.injective).mono
  rintro t ⟨k, rfl⟩
  exact ⟨hA k, hB k⟩

/-- On every qualifying record enumeration, both finite distance differences
are eventually constant, with values independent of the enumeration -/
theorem recordSequence_eventual_busemann (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n) (hnzero : n 0 = 0)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j) (k : ℕ) :
    let hL := recordSequence_L_nonneg w n hnzero hB
    let hS := recordSequence_records_infinite w n hn hA hB
    ∃ M : ℕ, ∀ m, M ≤ m →
      RecordDistanceDifference w true k (n m) (busemannUIQBOT_LDP w k hL hS) ∧
      RecordDistanceDifference w false k (n m) (busemannUIQBOT_SDP w k hL hS) := by
  dsimp only
  obtain ⟨N, hN⟩ := busemannUIQBOT_LDP_spec w k (recordSequence_L_nonneg w n hnzero hB)
    (recordSequence_records_infinite w n hn hA hB)
  obtain ⟨N', hN'⟩ := busemannUIQBOT_SDP_spec w k (recordSequence_L_nonneg w n hnzero hB)
    (recordSequence_records_infinite w n hn hA hB)
  refine ⟨max N N', fun m hm => ?_⟩
  have hmn : m ≤ n m := by
    have := hn.add_le_nat m 0
    simpa only [hnzero, Nat.add_zero] using this
  exact ⟨hN (n m) (by omega) (hA m) (hB m),
    hN' (n m) (by omega) (hA m) (hB m)⟩

/-- Every fixed boundary vertex eventually belongs to the old side and is
reachable from the source; from there it reaches each later record. This
also proves finiteness of the relevant actual path family -/
theorem recordSequence_boundary_reachability (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n) (hnzero : n 0 = 0)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j) (k : ℕ) :
    ∃ M : ℕ, ∀ m, M ≤ m →
      rightBoundaryVertex w k ∈ recordBefore w (n m) ∧
      Reachable (rightBoundaryVertex w 0) (rightBoundaryVertex w k) ∧
      Reachable (rightBoundaryVertex w k) (recordVertex w (n m)) ∧
      Finite (Path (rightBoundaryVertex w k) (recordVertex w (n m))) := by
  have hL := recordSequence_L_nonneg w n hnzero hB
  have hR := sequence_R_unbounded w n hn hnzero hA
  let a := natSelect (fun t => ∀ j, j < t → R w t < R w j) k
  refine ⟨a + 1, fun m hm => ?_⟩
  have hmn : m ≤ n m := by
    have := hn.add_le_nat m 0
    simpa only [hnzero, Nat.add_zero] using this
  have ham : a < n m := by omega
  have hbefore : rightBoundaryVertex w k ∈ recordBefore w (n m) := by
    rw [boundary_eq_record w hL hR k]
    exact record_mem_before w ham (hA m)
  exact ⟨hbefore, rightBoundaryVertex_reachable w hL hR k,
    before_reaches_record w hR (n m) (hA m) (hB m) _ hbefore,
    recordSequence_paths_finite w n hn hnzero hA hB _ _ ⟨n m, hbefore.1⟩⟩

/-- Almost surely the Pitman-flipped code has uniquely determined eventual
finite LDP and SDP differences for every right-boundary index. The record
barriers are written literally, and `∀ k` lies inside the almost-sure event -/
theorem pitmanCodes_ae_eventual_recordDifferences :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ k : ℕ, ∀ longest : Bool,
        ∃! v : ℤ, ∃ N : ℕ, ∀ t, N ≤ t →
          (∀ j < t, R w t ≤ R w j - 1) →
          (∀ j, t ≤ j → L w t ≤ L w j) →
          RecordDistanceDifference w longest k t v := by
  filter_upwards [pitmanCodes_ae_infinite_cutSeparation_records] with ω hS
  dsimp only
  intro k longest
  apply existsUnique_eventual_recordDifference _ _ hS longest k
  intro j
  rw [kmsw_L_eq]
  exact integrateCodes_pitmanCode_fst_nonneg _ j

/-- A single almost-sure event supplies a record sequence starting at zero,
right-boundary reachability, and the characterized LDP/SDP values for every
index simultaneously (`eqn-busemann-vertex`, -/
theorem pitmanCodes_ae_recordSequence_busemann :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ n : ℕ → ℕ, ∃ hn : StrictMono n, ∃ hnzero : n 0 = 0,
      ∃ hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1,
      ∃ hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j,
      ∀ k : ℕ, ∃ M : ℕ, ∀ m, M ≤ m →
        rightBoundaryVertex w k ∈ recordBefore w (n m) ∧
        Reachable (rightBoundaryVertex w 0) (rightBoundaryVertex w k) ∧
        Reachable (rightBoundaryVertex w k) (recordVertex w (n m)) ∧
        RecordDistanceDifference w true k (n m)
          (busemannUIQBOT_LDP w k (recordSequence_L_nonneg w n hnzero hB)
            (recordSequence_records_infinite w n hn hA hB)) ∧
        RecordDistanceDifference w false k (n m)
          (busemannUIQBOT_SDP w k (recordSequence_L_nonneg w n hnzero hB)
            (recordSequence_records_infinite w n hn hA hB)) := by
  filter_upwards [pitmanCodes_ae_infinite_cutSeparation_records] with ω hS
  dsimp only
  let w := pitmanCode (fun i => ω (i + 1))
  have hL : ∀ j, 0 ≤ L w j := by
    intro j
    rw [kmsw_L_eq]
    exact integrateCodes_pitmanCode_fst_nonneg _ j
  obtain ⟨n, hn, hnzero, hnr⟩ := infinite_natSet_exists_enumeration_zero _ hS
    (zero_mem_records_of_L_nonneg w hL)
  have hrec (i : ℕ) : (∀ j < n i, R w (n i) ≤ R w j - 1) ∧
      ∀ j, n i ≤ j → L w (n i) ≤ L w j := by
    have hm : n i ∈ Set.range n := ⟨i, rfl⟩
    rw [hnr] at hm
    exact hm
  let hA := fun k => (hrec k).1
  let hB := fun k => (hrec k).2
  refine ⟨n, hn, hnzero, hA, hB, fun k => ?_⟩
  obtain ⟨N, hN⟩ := recordSequence_boundary_reachability w n hn hnzero hA hB k
  obtain ⟨N', hN'⟩ := recordSequence_eventual_busemann w n hn hnzero hA hB k
  refine ⟨max N N', fun m hm => ?_⟩
  obtain ⟨hb, hr, hr', _⟩ := hN m (by omega)
  obtain ⟨hd, hd'⟩ := hN' m (by omega)
  exact ⟨hb, hr, hr', hd, hd'⟩

end DirectedDistances.KMSW
