module

public import DirectedDistances.PlanarMap.D39MapCore
public import DirectedDistances.PlanarMap.CyclicRestriction

public section
namespace DirectedDistances.PlanarMap

open Equiv

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The vertex
represented by a dart of a rooted locally finite map. Source: -/
@[expose] def d39VertexClass (M : D39RootedMap)
    (d : M.core.D) : RootedLocallyFiniteVertex M.core.D M.core.rot :=
  rootedLocallyFiniteVertexClass M.core.rot d

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Darts incident -/
@[expose] def d39VertexDarts (M : D39RootedMap)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) : Set M.core.D :=
  {d | d39VertexClass M d = v}

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Local -/
theorem d39VertexDarts_finite (M : D39RootedMap)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    (d39VertexDarts M v).Finite := by
  classical
  let d := Quotient.out v
  have hd : rootedLocallyFiniteVertexClass M.core.rot d = v := Quotient.out_eq' v
  have heq : {e : M.core.D | M.core.rot.SameCycle d e} = d39VertexDarts M v := by
    ext e
    constructor
    · intro he
      change rootedLocallyFiniteVertexClass M.core.rot e = v
      exact (Quotient.sound he).symm.trans hd
    · intro he
      change rootedLocallyFiniteVertexClass M.core.rot e = v at he
      exact Quotient.exact (hd.trans he.symm)
  rw [← heq]
  exact M.core.locallyFinite d

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The finite set -/
@[expose] noncomputable def d39VertexDartFinset
    (M : D39RootedMap)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) : Finset M.core.D := by
  classical
  exact (d39VertexDarts_finite M v).toFinset

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Membership in -/
theorem mem_d39VertexDartFinset (M : D39RootedMap)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) (d : M.core.D) :
    d ∈ d39VertexDartFinset M v ↔
      d39VertexClass M d = v := by
  classical
  simp [d39VertexDartFinset, d39VertexDarts]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The finite set
of geometric neighbors of a vertex, using every edge, including missing edges. Source: -/
@[expose] noncomputable def d39Neighbors
    (M : D39RootedMap)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    Finset (RootedLocallyFiniteVertex M.core.D M.core.rot) := by
  classical
  exact (d39VertexDartFinset M v).image
    (fun d => d39VertexClass M (M.core.edgeInv d))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The neighbor
set is exactly the geometric edge endpoints incident to a vertex. Source: -/
theorem mem_d39Neighbors (M : D39RootedMap)
    (v w : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    w ∈ d39Neighbors M v ↔
      ∃ d, d39VertexClass M d = v ∧
        d39VertexClass M (M.core.edgeInv d) = w := by
  classical
  simp [d39Neighbors, mem_d39VertexDartFinset]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Reachability by
at most `r` all-geometric edges from the root vertex. Source: -/
inductive D39WithinRadius (M : D39RootedMap) :
    ℕ → RootedLocallyFiniteVertex M.core.D M.core.rot → Prop
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The root is -/
  | root : D39WithinRadius M 0
      (d39VertexClass M M.rootMark.dart)
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Enlarging the -/
  | stay {r v} : D39WithinRadius M r v →
      D39WithinRadius M (r + 1) v
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. One -/
  | edge {r v w} : D39WithinRadius M r v →
      rootedLocallyFiniteGeometricStep M.core.rot M.core.edgeInv v w →
      D39WithinRadius M (r + 1) w

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The finite
statements use 0 < r (index r + 1). -/
@[expose] noncomputable def d39BallVertices
    (M : D39RootedMap) :
    ℕ → Finset (RootedLocallyFiniteVertex M.core.D M.core.rot)
  | 0 => by
      classical
      exact {d39VertexClass M M.rootMark.dart}
  | r + 1 => by
      classical
      exact d39BallVertices M r ∪
        (d39BallVertices M r).biUnion
          (d39Neighbors M)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Radius vertices
are exactly those reached by at most that many all-geometric edges. Source: -/
theorem mem_d39BallVertices (M : D39RootedMap)
    (r : ℕ) (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    v ∈ d39BallVertices M r ↔
      D39WithinRadius M r v := by
  classical
  induction r generalizing v with
  | zero =>
      constructor
      · intro h
        have hv : v = d39VertexClass M M.rootMark.dart := by
          simpa [d39BallVertices] using h
        subst v
        exact .root
      · intro h
        cases h with
        | root => simp [d39BallVertices]
  | succ r ih =>
      change v ∈ d39BallVertices M r ∪
        (d39BallVertices M r).biUnion
          (d39Neighbors M) ↔ _
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · exact .stay ((ih v).mp h)
        · rcases Finset.mem_biUnion.mp h with ⟨u, hu, hv⟩
          rcases (mem_d39Neighbors M u v).mp hv with
            ⟨d, hd, he⟩
          exact .edge ((ih u).mp hu) ⟨d, hd, he⟩
      · intro h
        cases h with
        | stay hprev =>
            exact Finset.mem_union_left _ ((ih v).mpr hprev)
        | edge hprev hedge =>
            apply Finset.mem_union_right
            apply Finset.mem_biUnion.mpr
            refine ⟨_, (ih _).mpr hprev, ?_⟩
            exact (mem_d39Neighbors M _ _).mpr hedge

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Darts in the
induced all-geometric radius ball: both endpoints lie within radius `r` of the root vertex. The
dart component preserves geometric edge identities and both endpoint bounds. Source: -/
@[expose] noncomputable def d39BallDarts
    (M : D39RootedMap) (r : ℕ) : Finset M.core.D := by
  classical
  let V := d39BallVertices M r
  let S := V.biUnion (d39VertexDartFinset M)
  exact S.filter fun d => d39VertexClass M (M.core.edgeInv d) ∈ V

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The finite dart
set has exactly the two all-geometric endpoint bounds required by Definition 3.8. Source: -/
theorem mem_d39BallDarts (M : D39RootedMap)
    (r : ℕ) (d : M.core.D) :
    d ∈ d39BallDarts M r ↔
      d39VertexClass M d ∈ d39BallVertices M r ∧
      d39VertexClass M (M.core.edgeInv d) ∈
        d39BallVertices M r := by
  classical
  simp only [d39BallDarts, Finset.mem_filter,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨v, hv, hd⟩, he⟩
    have hsource := (mem_d39VertexDartFinset M v d).mp hd
    exact ⟨hsource ▸ hv, he⟩
  · rintro ⟨hd, he⟩
    refine ⟨⟨d39VertexClass M d, hd, ?_⟩, he⟩
    exact (mem_d39VertexDartFinset M _ _).mpr rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Local -/
theorem d39RotationReturn (M : D39RootedMap) (d : M.core.D) :
    ∃ k : ℕ, 0 < k ∧ (M.core.rot ^ k) d = d := by
  classical
  let O := d39VertexDartFinset M
    (d39VertexClass M d)
  have hd : d ∈ O := by
    simp [O, mem_d39VertexDartFinset]
  have hrot : ∀ x : M.core.D, M.core.rot x ∈ O ↔ x ∈ O := by
    intro x
    change M.core.rot x ∈ d39VertexDartFinset M
        (d39VertexClass M d) ↔
      x ∈ d39VertexDartFinset M
        (d39VertexClass M d)
    rw [mem_d39VertexDartFinset,
      mem_d39VertexDartFinset]
    have hcycle : M.core.rot.SameCycle (M.core.rot x) x :=
      Equiv.Perm.SameCycle.rfl.apply_left
    have hclass : d39VertexClass M (M.core.rot x) =
        d39VertexClass M x := Quotient.sound hcycle
    constructor
    · intro hx
      exact hclass.symm.trans hx
    · intro hx
      exact hclass.trans hx
  let ρ : Equiv.Perm O := M.core.rot.subtypePerm hrot
  let x : O := ⟨d, hd⟩
  refine ⟨orderOf ρ, orderOf_pos ρ, ?_⟩
  have hpow (n : ℕ) : ((ρ ^ n) x).1 = (M.core.rot ^ n) d := by
    induction n with
    | zero => rfl
    | succ n ih =>
        calc
          ((ρ ^ (n + 1)) x).1 = (ρ ((ρ ^ n) x)).1 := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = M.core.rot ((M.core.rot ^ n) d) := by
            simp only [ρ, Equiv.Perm.subtypePerm_apply, ih]
          _ = (M.core.rot ^ (n + 1)) d := by
            rw [pow_succ', Equiv.Perm.mul_apply]
  have hone : ρ ^ orderOf ρ = 1 := pow_orderOf_eq_one ρ
  have hval : ((ρ ^ orderOf ρ) x).1 = d := by rw [hone]; rfl
  exact (hpow (orderOf ρ)).symm.trans hval

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallVertices_mono (M : D39RootedMap) {r s : ℕ} (hrs : r ≤ s) :
    d39BallVertices M r ⊆ d39BallVertices M s := by
  intro v hv
  rw [mem_d39BallVertices] at hv ⊢
  induction s generalizing r v with
  | zero =>
      have hr : r = 0 := by omega
      subst r
      exact hv
  | succ s ih =>
      by_cases h : r ≤ s
      · exact .stay (ih h hv)
      · have hr : r = s + 1 := by omega
        subst r
        exact hv

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallDarts_mono (M : D39RootedMap) {r s : ℕ} (hrs : r ≤ s) :
    d39BallDarts M r ⊆ d39BallDarts M s := by
  intro d hd
  rw [mem_d39BallDarts] at hd ⊢
  exact ⟨d39BallVertices_mono M hrs hd.1, d39BallVertices_mono M hrs hd.2⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallVertices_finite (M : D39RootedMap) (r : ℕ) :
    (d39BallVertices M r : Set (RootedLocallyFiniteVertex M.core.D M.core.rot)).Finite :=
  (d39BallVertices M r).finite_toSet

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallDarts_finite (M : D39RootedMap) (r : ℕ) :
    (d39BallDarts M r : Set M.core.D).Finite :=
  (d39BallDarts M r).finite_toSet

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallDarts_edgeInv_closed (M : D39RootedMap) (r : ℕ) (d : M.core.D)
    (hd : d ∈ d39BallDarts M r) : M.core.edgeInv d ∈ d39BallDarts M r := by
  rw [mem_d39BallDarts] at hd ⊢
  simpa only [M.core.edgeInv_invol] using hd.symm

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
every positive radius, irrespective of missingness. -/
theorem d39BallDarts_root_mem (M : D39RootedMap) {r : ℕ} (hr : 0 < r) :
    M.rootMark.dart ∈ d39BallDarts M r ∧
      M.core.edgeInv M.rootMark.dart ∈ d39BallDarts M r := by
  have hzero : d39VertexClass M M.rootMark.dart ∈ d39BallVertices M 0 := by
    classical
    simp [d39BallVertices]
  have hone : d39VertexClass M (M.core.edgeInv M.rootMark.dart) ∈
      d39BallVertices M 1 := by
    rw [mem_d39BallVertices]
    exact .edge .root ⟨M.rootMark.dart, rfl, rfl⟩
  have hroot := d39BallVertices_mono M (Nat.zero_le r) hzero
  have hopp := d39BallVertices_mono M (Nat.succ_le_iff.mpr hr) hone
  have hd := (mem_d39BallDarts M r M.rootMark.dart).mpr ⟨hroot, hopp⟩
  exact ⟨hd, d39BallDarts_edgeInv_closed M r _ hd⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
rotation, preserving every retained edge identity. Radius 0 is only the internal recursion base, -/
@[expose] noncomputable def d39BallMap (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}] :
    CombinatorialMap {d : M.core.D // d ∈ d39BallDarts M r} := by
  classical
  let S := d39BallDarts M r
  have hflip : ∀ d : M.core.D, M.core.edgeInv d ∈ S ↔ d ∈ S := by
    intro d
    constructor
    · intro hd
      have h := d39BallDarts_edgeInv_closed M r (M.core.edgeInv d) hd
      simpa only [M.core.edgeInv_invol] using h
    · exact d39BallDarts_edgeInv_closed M r d
  have hreturn : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.core.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, heq⟩ := d39RotationReturn M x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  exact
    { edgeInv := M.core.edgeInv.subtypePerm hflip
      edgeInv_invol := by
        intro d
        apply Subtype.ext
        exact M.core.edgeInv_invol d.1
      edgeInv_ne := by
        intro d hd
        exact M.core.edgeInv_ne d.1 (congrArg Subtype.val hd)
      rot := cyclicFirstReturn M.core.rot S hreturn }

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
@[expose] def d39BallMissing (M : D39RootedMap) (r : ℕ)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) : Prop := M.core.missing d.1

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
@[expose] def d39BallTail (M : D39RootedMap) (r : ℕ)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) : Prop := M.core.tail d.1

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallTail_missing (M : D39RootedMap) (r : ℕ)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39BallMissing M r d → ¬ d39BallTail M r d := M.core.tail_missing d.1

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
use 0 < r (index r + 1). -/
inductive D39BallRootMark (M : D39RootedMap) (r : ℕ) where
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.   Source: -/
  | present (d : {d : M.core.D // d ∈ d39BallDarts M r})
      (hp : ¬ d39BallMissing M r d) (ht : d39BallTail M r d)
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.   Source: -/
  | missing (d : {d : M.core.D // d ∈ d39BallDarts M r}) (hm : d39BallMissing M r d)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
@[expose] def d39BallRootMark (M : D39RootedMap) (r : ℕ) (hr : 0 < r) :
    D39BallRootMark M r :=
  match h : M.rootMark with
  | .present d hp ht =>
      .present ⟨d, by simpa [h, D39RootMark.dart] using (d39BallDarts_root_mem M hr).1⟩
        hp ht
  | .missing d hm =>
      .missing ⟨d, by simpa [h, D39RootMark.dart] using (d39BallDarts_root_mem M hr).1⟩ hm

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
has no global plane embedding or planarity property; rotation systems alone can have positive
genus. This Prop is never assumed. -/
@[expose] def D39BallGenusZero (M : D39RootedMap) (r : ℕ) : Prop :=
  letI : DecidableEq {d : M.core.D // d ∈ d39BallDarts M r} := Classical.decEq _
  (d39BallMap M r).eulerChar = 2

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39Vertex_reachable (M : D39RootedMap) (d : M.core.D) :
    ∃ r, D39WithinRadius M r (d39VertexClass M d) := by
  have hconn := M.core.connected M.rootMark.dart d
  induction hconn with
  | refl => exact ⟨0, .root⟩
  | @tail a b hpath hstep ih =>
      obtain ⟨r, hr⟩ := ih
      rcases hstep with hrot | hrot | hedge | hedge
      · rw [hrot]
        refine ⟨r, ?_⟩
        have heq : d39VertexClass M (M.core.rot a) = d39VertexClass M a :=
          Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left
        rw [heq]
        exact hr
      · rw [hrot]
        refine ⟨r, ?_⟩
        have heq : d39VertexClass M (M.core.rot.symm a) = d39VertexClass M a :=
          Quotient.sound Equiv.Perm.SameCycle.rfl.symm_apply_left
        rw [heq]
        exact hr
      · rw [hedge]
        exact ⟨r + 1, .edge hr ⟨_, rfl, rfl⟩⟩
      · have hinv (x : M.core.D) : M.core.edgeInv.symm x = M.core.edgeInv x := by
          apply M.core.edgeInv.injective
          simp [M.core.edgeInv_invol]
        rw [hinv] at hedge
        rw [hedge]
        exact ⟨r + 1, .edge hr ⟨_, rfl, rfl⟩⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallDarts_exhaust (M : D39RootedMap) (d : M.core.D) :
    ∃ r, d ∈ d39BallDarts M r := by
  obtain ⟨r, hr⟩ := d39Vertex_reachable M d
  obtain ⟨s, hs⟩ := d39Vertex_reachable M (M.core.edgeInv d)
  refine ⟨max r s, (mem_d39BallDarts M _ d).2 ⟨?_, ?_⟩⟩
  · exact d39BallVertices_mono M (le_max_left r s)
      ((mem_d39BallVertices M r _).2 hr)
  · exact d39BallVertices_mono M (le_max_right r s)
      ((mem_d39BallVertices M s _).2 hs)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallDarts_capture_finite (M : D39RootedMap) (r : ℕ) (S : Finset M.core.D) :
    ∃ R, r ≤ R ∧ ∀ d ∈ S, d ∈ d39BallDarts M R := by
  classical
  choose radius hradius using d39BallDarts_exhaust M
  let R := max r (S.sup radius)
  refine ⟨R, le_max_left _ _, ?_⟩
  intro d hd
  exact d39BallDarts_mono M
    (le_trans (Finset.le_sup hd) (le_max_right _ _)) (hradius d)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
face successor, by the first-return construction. -/
theorem d39Ball_faceSucc_of_mem (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hface : M.core.rot.symm (M.core.edgeInv d.1) ∈ d39BallDarts M r) :
    ((d39BallMap M r).faceSucc d).1 = M.core.rot.symm (M.core.edgeInv d.1) := by
  classical
  let S := d39BallDarts M r
  let N := d39BallMap M r
  let y : S := ⟨M.core.rot.symm (M.core.edgeInv d.1), hface⟩
  have hret : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.core.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, heq⟩ := d39RotationReturn M x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have hnext : M.core.rot y.1 = M.core.edgeInv d.1 := M.core.rot.apply_symm_apply _
  have hy : M.core.rot y.1 ∈ S := hnext.symm ▸
    d39BallDarts_edgeInv_closed M r d.1 d.2
  have hrot : N.rot y = N.edgeInv d := by
    apply Subtype.ext
    have hone : (cyclicFirstReturn M.core.rot S hret y).1 = M.core.rot y.1 := by
      have htime : cyclicFirstReturnTime M.core.rot S hret y = 1 := by
        apply le_antisymm
        · exact Nat.find_min' (hret y) ⟨Nat.one_pos, by simpa using hy⟩
        · exact (cyclicFirstReturnTime_spec M.core.rot S hret y).1
      rw [(firstReturn_spec M.core.rot S hret y).1, htime, pow_one]
    exact hone.trans hnext
  change (N.rot.symm (N.edgeInv d)).1 = _
  rw [← hrot, Equiv.symm_apply_apply]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
this does not select newly created finite-map faces. Radius 0 is only the internal recursion base, -/
@[expose] def d39BallContainsOriginalFace (M : D39RootedMap) (r : ℕ)
    (d : M.core.D) : Prop :=
  ∀ e, Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e → e ∈ d39BallDarts M r

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
successor. -/
theorem d39Ball_faceSucc_of_contained (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hface : d39BallContainsOriginalFace M r d.1) :
    ((d39BallMap M r).faceSucc d).1 = M.core.rot.symm (M.core.edgeInv d.1) := by
  apply d39Ball_faceSucc_of_mem
  exact hface _ Equiv.Perm.SameCycle.rfl.apply_right

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
endpoints on a single face, in a sufficiently large ball. -/
theorem d39Ball_capture_face_path (M : D39RootedMap) (r : ℕ) (x : M.core.D) (n : ℕ) :
    ∃ R, r ≤ R ∧ ∃ hx : x ∈ d39BallDarts M R,
      ∃ hy : ((M.core.rot.symm * M.core.edgeInv) ^ n) x ∈ d39BallDarts M R,
        letI : DecidableEq {d : M.core.D // d ∈ d39BallDarts M R} := Classical.decEq _
        (d39BallMap M R).faceSucc.SameCycle ⟨x, hx⟩
          ⟨((M.core.rot.symm * M.core.edgeInv) ^ n) x, hy⟩ := by
  classical
  let f : Equiv.Perm M.core.D := M.core.rot.symm * M.core.edgeInv
  let S := (Finset.range (n + 1)).image fun i => (f ^ i) x
  obtain ⟨R, hrR, hR⟩ := d39BallDarts_capture_finite M r S
  let _ : DecidableEq {d : M.core.D // d ∈ d39BallDarts M R} := Classical.decEq _
  have hmem (i : ℕ) (hi : i ≤ n) : (f ^ i) x ∈ d39BallDarts M R := by
    apply hR
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  have hx : x ∈ d39BallDarts M R := by simpa using hmem 0 (Nat.zero_le n)
  refine ⟨R, hrR, hx, hmem n le_rfl, ?_⟩
  let B := d39BallMap M R
  let z : {d : M.core.D // d ∈ d39BallDarts M R} := ⟨x, hx⟩
  have hpow : ∀ i, i ≤ n → ((B.faceSucc ^ i) z).1 = (f ^ i) x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
        intro hi
        have hv := ih (by omega)
        have hnxt : M.core.rot.symm (M.core.edgeInv ((B.faceSucc ^ i) z).1) ∈
            d39BallDarts M R := by
          rw [hv]
          simpa only [f, pow_succ', Equiv.Perm.mul_apply] using hmem (i + 1) hi
        rw [pow_succ', Equiv.Perm.mul_apply]
        rw [d39Ball_faceSucc_of_mem M R _ hnxt, hv]
        rw [pow_succ', Equiv.Perm.mul_apply]
        rfl
  refine ⟨(n : ℤ), ?_⟩
  apply Subtype.ext
  exact hpow n le_rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
on a common face of a sufficiently large ball. This follows from finite face-path capture and does
not assume ball planarity. -/
theorem d39Ball_outerFace_captured_in_larger_ball (M : D39RootedMap) (r : ℕ)
    (d : M.core.D)
    (hd : Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) M.core.outer d) :
    ∃ R, r ≤ R ∧ ∃ ho : M.core.outer ∈ d39BallDarts M R,
      ∃ hdR : d ∈ d39BallDarts M R,
        letI : DecidableEq {e : M.core.D // e ∈ d39BallDarts M R} := Classical.decEq _
        (d39BallMap M R).IsOuter ⟨M.core.outer, ho⟩ ⟨d, hdR⟩ := by
  classical
  let f : Equiv.Perm M.core.D := M.core.rot.symm * M.core.edgeInv
  rcases hd with ⟨i, hi⟩
  cases i with
  | ofNat n =>
      have heq : (f ^ n) M.core.outer = d := by simpa using hi
      obtain ⟨R, hrR, ho, hn, hcycle⟩ := d39Ball_capture_face_path M r M.core.outer n
      let _ : DecidableEq {e : M.core.D // e ∈ d39BallDarts M R} := Classical.decEq _
      refine ⟨R, hrR, ho, heq ▸ hn, ?_⟩
      change (d39BallMap M R).faceSucc.SameCycle
        ⟨M.core.outer, ho⟩ ⟨(f ^ n) M.core.outer, hn⟩ at hcycle
      simpa only [CombinatorialMap.IsOuter, heq] using hcycle
  | negSucc n =>
      have heq : (f ^ (n + 1)) d = M.core.outer := by
        rw [← hi, zpow_negSucc]
        exact (f ^ (n + 1)).apply_symm_apply _
      obtain ⟨R, hrR, hdR, hn, hcycle⟩ := d39Ball_capture_face_path M r d (n + 1)
      let _ : DecidableEq {e : M.core.D // e ∈ d39BallDarts M R} := Classical.decEq _
      refine ⟨R, hrR, heq ▸ hn, hdR, ?_⟩
      have hcycle' := hcycle.symm
      change (d39BallMap M R).faceSucc.SameCycle
        ⟨(f ^ (n + 1)) d, hn⟩ ⟨d, hdR⟩ at hcycle'
      simpa only [CombinatorialMap.IsOuter, heq] using hcycle'

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The restricted
rotation has the same vertex cycles as the ambient rotation. Source: -/
theorem d39Ball_rot_sameCycle_iff
    (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    (x y : {d : M.core.D // d ∈ d39BallDarts M r}) :
    (d39BallMap M r).rot.SameCycle x y ↔
      M.core.rot.SameCycle x.1 y.1 := by
  classical
  let S := d39BallDarts M r
  let hreturn : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.core.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, hperiod⟩ := d39RotationReturn M x.1
    exact ⟨k, hk, by rw [hperiod]; exact x.2⟩
  change (cyclicFirstReturn M.core.rot S hreturn).SameCycle x y ↔ _
  exact firstReturn_sameCycle_iff M.core.rot S hreturn x y

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. One step in
the relation generated by rotation and edge involution. Source: -/
private def d39BallStep {D : Type} [Fintype D]
    [DecidableEq D] (M : CombinatorialMap D) (x y : D) : Prop :=
  y = M.rot x ∨ y = M.rot.symm x ∨
    y = M.edgeInv x ∨ y = M.edgeInv.symm x

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Rotation along
one cycle is reachable by repeated `d39BallStep` steps. Source: -/
private theorem d39BallRotation_reachable
    {D : Type} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)
    {x y : D} (h : M.rot.SameCycle x y) :
    Relation.ReflTransGen (d39BallStep M) x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ n, Relation.ReflTransGen (d39BallStep M)
      x ((M.rot ^ n) x) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.tail (Or.inl rfl)
  rw [← hn]
  exact hpow n

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The root dart -/
private theorem d39BallRoot_mem (M : D39RootedMap)
    (r : ℕ) (hr : 0 < r) : M.rootMark.dart ∈ d39BallDarts M r :=
  (d39BallDarts_root_mem M hr).1

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. The edge -/
private theorem d39Ball_edgeInv_symm
    {D : Type} [Fintype D] [DecidableEq D] (C : CombinatorialMap D) (d : D) :
    C.edgeInv.symm d = C.edgeInv d := by
  apply C.edgeInv.injective
  simp [C.edgeInv_invol]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. A bounded
ambient path reaches its dart in the restricted ball relation. Source: -/
private theorem d39BallPath_reaches (M : D39RootedMap)
    (r : ℕ) (hr : 0 < r)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    {v : RootedLocallyFiniteVertex M.core.D M.core.rot} {n : ℕ}
    (hp : D39WithinRadius M n v) (hn : n ≤ r)
    (d : M.core.D) (hd : d ∈ d39BallDarts M r)
    (hvertex : d39VertexClass M d = v) :
    Relation.ReflTransGen
      (d39BallStep
        (d39BallMap M r))
      ⟨M.rootMark.dart, d39BallRoot_mem M r hr⟩ ⟨d, hd⟩ := by
  classical
  let S := d39BallDarts M r
  let hflip : ∀ d, d ∈ S → M.core.edgeInv d ∈ S :=
    fun d hd => d39BallDarts_edgeInv_closed M r d hd
  let N := d39BallMap M r
  revert hn d hd hvertex
  induction hp with
  | root =>
      intro hn d hd hvertex
      have hcycle : M.core.rot.SameCycle M.rootMark.dart d :=
        (Quotient.exact hvertex).symm
      have hcycleN : N.rot.SameCycle
          (⟨M.rootMark.dart, d39BallRoot_mem M r hr⟩ :
            {d : M.core.D // d ∈ S}) ⟨d, hd⟩ := by
        exact (d39Ball_rot_sameCycle_iff M r _ _).2 hcycle
      exact d39BallRotation_reachable N hcycleN
  | @stay n v hp ih =>
      intro hn d hd hvertex
      exact ih (by omega) d hd hvertex
  | @edge n v w hp hstep ih =>
      intro hn d hd hvertex
      rcases hstep with ⟨e, hev, hew⟩
      have hn' : n ≤ r := by omega
      have hw : v ∈ d39BallVertices M r := by
        exact d39BallVertices_mono M hn'
          ((mem_d39BallVertices M n v).2 hp)
      have hz : w ∈ d39BallVertices M r := by
        exact d39BallVertices_mono M hn
          ((mem_d39BallVertices M (n + 1) w).2
            (D39WithinRadius.edge hp ⟨e, hev, hew⟩))
      have heS : e ∈ S := by
        apply (mem_d39BallDarts M r e).2
        constructor
        · change rootedLocallyFiniteVertexClass M.core.rot e ∈ _
          exact hev ▸ hw
        · change rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv e) ∈ _
          exact hew ▸ hz
      have hreach := ih hn' e heS hev
      have hedge : N.edgeInv (⟨e, heS⟩ : {d : M.core.D // d ∈ S}) =
          ⟨M.core.edgeInv e, hflip e heS⟩ := by
        apply Subtype.ext
        rfl
      have hflipstep : Relation.ReflTransGen
          (d39BallStep N) (⟨e, heS⟩ : {d : M.core.D // d ∈ S})
          ⟨M.core.edgeInv e, hflip e heS⟩ :=
        Relation.ReflTransGen.single (Or.inr (Or.inr (Or.inl hedge)))
      have hcycle : M.core.rot.SameCycle (M.core.edgeInv e) d :=
        Quotient.exact (hew.trans hvertex.symm)
      have hcycleN : N.rot.SameCycle ⟨M.core.edgeInv e, hflip e heS⟩ ⟨d, hd⟩ :=
        (d39Ball_rot_sameCycle_iff M r _ _).2 hcycle
      exact hreach.trans (hflipstep.trans
        (d39BallRotation_reachable N hcycleN))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Every
positive-radius induced rooted ball is connected by rotations and edge reversals. Source: -/
theorem d39BallMap_connected
    (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}] :
    (d39BallMap M r).IsConnected := by
  classical
  let S := d39BallDarts M r
  let N := d39BallMap M r
  have hsymmetric : Std.Symm (d39BallStep N) := ⟨by
    intro x y hxy
    rcases hxy with hxy | hxy | hxy | hxy
    · exact Or.inr (Or.inl (by simp [hxy]))
    · exact Or.inl (by simp [hxy])
    · exact Or.inr (Or.inr (Or.inr (by simp [hxy])))
    · exact Or.inr (Or.inr (Or.inl (by simp [hxy])))⟩
  intro x y
  have hxmem := (mem_d39BallDarts M r x.1).1 x.2
  have hymem := (mem_d39BallDarts M r y.1).1 y.2
  have hpx := (mem_d39BallVertices M r _).1 hxmem.1
  have hpy := (mem_d39BallVertices M r _).1 hymem.1
  have hreachx := d39BallPath_reaches M r hr hpx
    (Nat.le_refl r) x.1 x.2 rfl
  have hreachy := d39BallPath_reaches M r hr hpy
    (Nat.le_refl r) y.1 y.2 rfl
  have hreverseSymm : Std.Symm
      (Relation.ReflTransGen (d39BallStep N)) :=
    @Relation.ReflTransGen.stdSymm _ _ hsymmetric
  exact (hreverseSymm.symm
    (⟨M.rootMark.dart, d39BallRoot_mem M r hr⟩ :
      {d : M.core.D // d ∈ S}) x hreachx).trans hreachy


/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
ordered root mark. -/
theorem d39BallVertices_zero (M : D39RootedMap) :
    d39BallVertices M 0 = {M.rootMark.firstVertex} := by
  classical
  rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallMap_edgeInv (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    ((d39BallMap M r).edgeInv d).1 = M.core.edgeInv d.1 := rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
theorem d39BallMissing_edgeInv (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39BallMissing M r d ↔ d39BallMissing M r ((d39BallMap M r).edgeInv d) :=
  M.core.missing_edgeInv d.1

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
tail. -/
theorem d39BallTail_iff (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) (hp : ¬ d39BallMissing M r d) :
    d39BallTail M r d ↔ ¬ d39BallTail M r ((d39BallMap M r).edgeInv d) :=
  M.core.tail_iff d.1 hp

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source: -/
@[expose] def D39BallRootMark.toAmbient {M : D39RootedMap} {r : ℕ}
    (m : D39BallRootMark M r) : D39RootMark M.core :=
  match m with
  | .present d hp ht => .present d.1 hp ht
  | .missing d hm => .missing d.1 hm

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
constructor, is unchanged by restriction. -/
theorem d39BallRootMark_toAmbient (M : D39RootedMap) (r : ℕ) (hr : 0 < r) :
    (d39BallRootMark M r hr).toAmbient = M.rootMark := by
  cases M with
  | mk c m => cases m <;> rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
every ambient boundary vertex is retained. Radius 0 is only the internal recursion base, not a -/
theorem d39BallContainsOriginalFace_iff (M : D39RootedMap) (r : ℕ) (d : M.core.D) :
    d39BallContainsOriginalFace M r d ↔
      ∀ e, Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e →
        d39VertexClass M e ∈ d39BallVertices M r := by
  constructor
  · intro h e he
    exact ((mem_d39BallDarts M r e).1 (h e he)).1
  · intro h e he
    apply (mem_d39BallDarts M r e).2
    refine ⟨h e he, ?_⟩
    have hn := h (M.core.rot.symm (M.core.edgeInv e)) he.apply_right
    have hv : d39VertexClass M (M.core.rot.symm (M.core.edgeInv e)) =
        d39VertexClass M (M.core.edgeInv e) :=
      Quotient.sound Equiv.Perm.SameCycle.rfl.symm_apply_left
    rwa [hv] at hn

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result. Source:
condition remains. No global planarity datum is encoded by `D39MapCore`, and the isolated Prop is
not assumed by any construction. -/
theorem d39Ball_isPlanar_iff (M : D39RootedMap) (r : ℕ) (hr : 0 < r) :
    letI : DecidableEq {d : M.core.D // d ∈ d39BallDarts M r} := Classical.decEq _
    (d39BallMap M r).IsPlanar ↔ D39BallGenusZero M r := by
  classical
  let _ : DecidableEq {d : M.core.D // d ∈ d39BallDarts M r} := Classical.decEq _
  exact ⟨fun h => h.2, fun h => ⟨d39BallMap_connected M r hr, h⟩⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
the construction recovers the existing all-geometric vertex balls exactly. -/
theorem d39BallVertices_toD39RootedMap (M : RootedLocallyFiniteMap) (r : ℕ) :
    d39BallVertices M.toD39RootedMap r = rootedLocallyFiniteRadiusVertices M r := by
  classical
  induction r with
  | zero =>
      change ({M.toD39RootedMap.rootMark.firstVertex} : Finset _) = {_}
      rw [M.toD39RootedMap_firstVertex]
      rfl
  | succ r ih =>
      change d39BallVertices M.toD39RootedMap r ∪
        (d39BallVertices M.toD39RootedMap r).biUnion (d39Neighbors M.toD39RootedMap) =
        rootedLocallyFiniteRadiusVertices M r ∪
          (rootedLocallyFiniteRadiusVertices M r).biUnion (rootedLocallyFiniteNeighbors M)
      rw [ih]
      rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
balls agree under the existing carrier's conversion. -/
theorem d39BallDarts_toD39RootedMap (M : RootedLocallyFiniteMap) (r : ℕ) :
    d39BallDarts M.toD39RootedMap r = rootedLocallyFiniteBallDarts M r := by
  classical
  unfold d39BallDarts rootedLocallyFiniteBallDarts
  rw [d39BallVertices_toD39RootedMap]
  rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
are stable under the induced finite map's face successor. -/
theorem d39BallContainsOriginalFace_faceSucc (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    (d : {d : M.core.D // d ∈ d39BallDarts M r})
    (hd : d39BallContainsOriginalFace M r d.1) :
    d39BallContainsOriginalFace M r ((d39BallMap M r).faceSucc d).1 := by
  rw [d39Ball_faceSucc_of_contained M r d hd]
  intro e he
  exact hd e he.of_apply_left

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
union of full finite face cycles, with inherited incidences. -/
theorem d39BallContainsOriginalFace_closed (M : D39RootedMap) (r : ℕ)
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39BallContainsOriginalFace M r ((d39BallMap M r).faceSucc d).1 ↔
      d39BallContainsOriginalFace M r d.1 := by
  let B := d39BallMap M r
  have hiter (n : ℕ) (x : {d : M.core.D // d ∈ d39BallDarts M r})
      (hx : d39BallContainsOriginalFace M r x.1) :
      d39BallContainsOriginalFace M r ((B.faceSucc ^ n) x).1 := by
    induction n with
    | zero => exact hx
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact d39BallContainsOriginalFace_faceSucc M r _ ih
  constructor
  · intro hd
    have hpos : 0 < orderOf B.faceSucc := orderOf_pos B.faceSucc
    have heq : (B.faceSucc ^ (orderOf B.faceSucc - 1)) (B.faceSucc d) = d := by
      change (B.faceSucc ^ (orderOf B.faceSucc - 1) * B.faceSucc) d = d
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
      rw [pow_orderOf_eq_one]
      rfl
    have h := hiter (orderOf B.faceSucc - 1) (B.faceSucc d) hd
    rwa [heq] at h
  · exact d39BallContainsOriginalFace_faceSucc M r d

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
the positive-radius ball is represented by its induced dart rotation system. -/
theorem d39BallVertices_iff_incident_dart (M : D39RootedMap) (r : ℕ) (hr : 0 < r)
    (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
    v ∈ d39BallVertices M r ↔
      ∃ d ∈ d39BallDarts M r, d39VertexClass M d = v := by
  constructor
  · intro hv
    have hp := (mem_d39BallVertices M r v).1 hv
    have haux {n w} (h : D39WithinRadius M n w) : n ≤ r →
        ∃ d ∈ d39BallDarts M r, d39VertexClass M d = w := by
      induction h with
      | root =>
          intro _
          exact ⟨M.rootMark.dart, (d39BallDarts_root_mem M hr).1, rfl⟩
      | @stay n w hp ih =>
          intro hn
          exact ih (by omega)
      | @edge n w z hp hedge ih =>
          intro hn
          rcases hedge with ⟨d, hdw, hdz⟩
          have hw : w ∈ d39BallVertices M r :=
            d39BallVertices_mono M (by omega)
              ((mem_d39BallVertices M n w).2 hp)
          have hz : z ∈ d39BallVertices M r :=
            d39BallVertices_mono M hn
              ((mem_d39BallVertices M (n + 1) z).2 (.edge hp ⟨d, hdw, hdz⟩))
          have hd : d ∈ d39BallDarts M r := by
            apply (mem_d39BallDarts M r d).2
            constructor
            · change rootedLocallyFiniteVertexClass M.core.rot d ∈ _
              rw [hdw]
              exact hw
            · change rootedLocallyFiniteVertexClass M.core.rot (M.core.edgeInv d) ∈ _
              rw [hdz]
              exact hz
          exact ⟨M.core.edgeInv d, d39BallDarts_edgeInv_closed M r d hd, hdz⟩
    exact haux hp le_rfl
  · rintro ⟨d, hd, rfl⟩
    exact ((mem_d39BallDarts M r d).1 hd).1

end DirectedDistances.PlanarMap
end
