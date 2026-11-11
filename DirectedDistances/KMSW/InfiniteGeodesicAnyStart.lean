module

public import DirectedDistances.KMSW.InfiniteGeodesicAE
public import DirectedDistances.KMSW.CutSeparationAnyStart

/-! # Infinite extremal present paths from arbitrary allocated vertices

All paths retain actual present edge IDs. -/

public section
namespace DirectedDistances.KMSW
open Quiver MeasureTheory DirectedDistances.RandomWalk

private theorem any_vertex_ext {w : ℕ → Fin 3} {u v : PresentVertex w}
    (h : u.id = v.id) : u = v := by
  cases u
  cases v
  cases h
  rfl

private theorem any_endpoint_before {w : ℕ → Fin 3} {n : ℕ}
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {u z : PresentVertex w} (p : Path u z) (hu : u ∈ recordBefore w n)
    (havoid : recordVertex w n ∉ p.vertices) : z ∈ recordBefore w n := by
  induction p with
  | nil => exact hu
  | @cons y z p e ih =>
    have hy : y ∈ recordBefore w n := ih (by
      intro hmem
      exact havoid (Path.mem_vertices_cons p e |>.2 (Or.inl hmem)))
    by_contra hz
    apply presentArrow_no_crossing w n hA hB e
    refine ⟨hy, hz, ?_⟩
    intro heq
    exact havoid (heq ▸ (Path.mem_vertices_cons p e |>.2 (Or.inr rfl)))

private theorem any_to_record_confined {w : ℕ → Fin 3} {n : ℕ}
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {u : PresentVertex w} (hu : u ∈ recordBefore w n)
    (p : Path u (recordVertex w n)) :
    ∀ z ∈ p.vertices, z ∈ recordBefore w n ∪ {recordVertex w n} := by
  intro z hz
  by_cases heq : z = recordVertex w n
  · exact Or.inr heq
  · left
    obtain ⟨p₁, p₂, _⟩ := p.exists_eq_comp_of_mem_vertices hz
    apply any_endpoint_before hA hB p₁ hu
    intro hv
    obtain ⟨q₁, q₂, _⟩ := p₁.exists_eq_comp_of_mem_vertices hv
    have hcycle := presentVertex_acyclic w _ (q₂.comp p₂)
    rw [Path.length_comp] at hcycle
    have hq₂ : q₂.length = 0 := by omega
    exact heq (q₂.eq_of_length_zero hq₂).symm


private theorem any_region_finite (w : ℕ → Fin 3) (n : ℕ) :
    (recordBefore w n ∪ {recordVertex w n}).Finite := by
  apply Set.Finite.union _ (Set.finite_singleton _)
  apply Set.Finite.subset (Set.finite_range
    (fun i : Fin (kmswStage w n).nextVertex => (⟨i.val⟩ : PresentVertex w)))
  intro u hu
  exact ⟨⟨u.id, hu.1⟩, any_vertex_ext rfl⟩

/-- Every path to a record from its old side stays in the same finite region -/
theorem allocated_path_to_record_confined (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    {x : PresentVertex w} (hx : x ∈ recordBefore w n ∪ {recordVertex w n})
    (p : Path x (recordVertex w n)) :
    ∀ z ∈ p.vertices, z ∈ recordBefore w n ∪ {recordVertex w n} := by
  rcases hx with hx | hx
  · exact any_to_record_confined hA hB hx p
  · change x = recordVertex w n at hx
    subst x
    have hz := presentVertex_acyclic w _ p
    cases p with
    | nil => simp
    | cons p e => simp only [Path.length_cons] at hz; omega

private theorem any_mem_comp_left {w : ℕ → Fin 3} {x y z : PresentVertex w}
    (p : Path x y) (q : Path y z) {u : PresentVertex w} (hu : u ∈ p.vertices) :
    u ∈ (p.comp q).vertices := by
  induction q with
  | nil => exact hu
  | cons q e ih => exact (Path.mem_vertices_cons (p.comp q) e).2 (Or.inl ih)

private theorem allocated_arbitrarily_long_paths (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (x : PresentVertex w)
    (hx : ∃ n, x.id < (kmswStage w n).nextVertex) :
    ∀ N, ∃ y, ∃ p : Path x y, p.length = N := by
  obtain ⟨e, _, hc, hs, hp⟩ :=
    allocated_vertex_has_infinite_path_of_R_unbounded w hR x.id hx
  have heq : (⟨edgeWest w (e 0)⟩ : PresentVertex w) = x := any_vertex_ext hs
  let v : ℕ → PresentVertex w := fun i => ⟨edgeWest w (e i)⟩
  have harrow (i : ℕ) : v i ⟶ v (i + 1) := ⟨e i, hp i, rfl, hc i⟩
  have hex : ∀ N, ∃ p : Path (v 0) (v N), p.length = N := by
    intro N
    induction N with
    | zero => exact ⟨.nil, rfl⟩
    | succ N ih =>
      obtain ⟨p, hl⟩ := ih
      exact ⟨p.cons (harrow N), by rw [Path.length_cons, hl]⟩
  intro N
  obtain ⟨p, hl⟩ := hex N
  exact ⟨v N, heq ▸ p, by cases heq; exact hl⟩

/-- An allocated vertex on the old side reaches the record through present
edges. Finite confinement and acyclicity force sufficiently long paths to hit -/
theorem allocated_reachable_record (w : ℕ → Fin 3) (n : ℕ)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (x : PresentVertex w) (halloc : ∃ m, x.id < (kmswStage w m).nextVertex)
    (hx : x ∈ recordBefore w n ∪ {recordVertex w n}) :
    Reachable x (recordVertex w n) := by
  classical
  rcases hx with hx | hx
  · let S := any_region_finite w n
    obtain ⟨y, p, hp⟩ := allocated_arbitrarily_long_paths w hR x halloc
      (S.toFinset.card + 1)
    by_cases hm : recordVertex w n ∈ p.vertices
    · obtain ⟨p₁, _, _⟩ := p.exists_eq_comp_of_mem_vertices hm
      exact ⟨p₁⟩
    · have hconf : ∀ z ∈ p.vertices, z ∈ recordBefore w n ∪ {recordVertex w n} := by
        intro z hz
        obtain ⟨p₁, p₂, heq⟩ := p.exists_eq_comp_of_mem_vertices hz
        apply Or.inl
        apply any_endpoint_before hA hB p₁ hx
        intro hmem
        apply hm
        rw [heq]
        exact any_mem_comp_left p₁ p₂ hmem
      have hsub : p.vertices.toFinset ⊆ S.toFinset := by
        intro z hz
        exact S.mem_toFinset.mpr (hconf z (List.mem_toFinset.mp hz))
      have hcard := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup (vertices_nodup_of_acyclic
        (presentVertex_acyclic w) p), Path.vertices_length, hp] at hcard
      omega
  · change x = recordVertex w n at hx
    subst x
    exact ⟨.nil⟩

/-- Both extremal paths from an allocated old-side start to the first record
exist, with longest-path attainment proved by finite confinement -/
theorem allocated_exists_extremal_to_record (w : ℕ → Fin 3) (n : ℕ)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (x : PresentVertex w) (halloc : ∃ m, x.id < (kmswStage w m).nextVertex)
    (hx : x ∈ recordBefore w n ∪ {recordVertex w n}) :
    (∃ p : Path x (recordVertex w n), IsLongest p) ∧
    (∃ p : Path x (recordVertex w n), IsShortest p) := by
  have hr := allocated_reachable_record w n hR hA hB x halloc hx
  exact ⟨exists_isLongest_of_finite_vertex_confinement (presentVertex_acyclic w)
    _ (any_region_finite w n) (allocated_path_to_record_confined w n hA hB hx) hr,
    exists_isShortest hr⟩


/-- Increasing strict vertical records force the vertical coordinate to be -/
theorem recordSequence_R_unbounded_any (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1) :
    ∀ a : ℤ, ∃ t, R w t ≤ a := by
  have hb : ∀ k, R w (n k) ≤ R w (n 0) - (k : ℤ) := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      have h := hA (k + 1) (n k) (hn (by omega))
      rw [Nat.cast_add, Nat.cast_one]
      omega
  intro a
  refine ⟨n ((R w (n 0) - a).natAbs), ?_⟩
  have ha := Int.le_natAbs (a := R w (n 0) - a)
  have hh := hb ((R w (n 0) - a).natAbs)
  omega

private theorem any_later_record_not_before (w : ℕ → Fin 3) {m n : ℕ}
    (hR : ∀ a : ℤ, ∃ t, R w t ≤ a) (hmn : m < n)
    (hAm : ∀ j < m, R w m ≤ R w j - 1)
    (hBm : ∀ j, m ≤ j → L w m ≤ L w j)
    (hAn : ∀ j < n, R w n ≤ R w j - 1) :
    recordVertex w n ∉ recordBefore w m := by
  intro hb
  obtain ⟨q⟩ := allocated_reachable_record w m hR hAm hBm
    (recordVertex w n) ⟨m, hb.1⟩ (Or.inl hb)
  obtain ⟨p⟩ := recordVertex_reachable w hmn hAm hAn
  have hz := presentVertex_acyclic w _ (p.comp q)
  rw [Path.length_comp] at hz
  have hp : p.length = 0 := by omega
  exact recordVertex_ne w hmn hAn (p.eq_of_length_zero hp)

private theorem any_start_mem_record (w : ℕ → Fin 3) {m n : ℕ}
    (hR : ∀ a : ℤ, ∃ t, R w t ≤ a) (hmn : m < n)
    (hAm : ∀ j < m, R w m ≤ R w j - 1)
    (hBm : ∀ j, m ≤ j → L w m ≤ L w j)
    (hAn : ∀ j < n, R w n ≤ R w j - 1)
    {x : PresentVertex w} (hx : x ∈ recordBefore w m ∪ {recordVertex w m})
    (p : Path x (recordVertex w n)) : recordVertex w m ∈ p.vertices := by
  rcases hx with hx | hx
  · by_contra hmiss
    exact any_later_record_not_before w hR hmn hAm hBm hAn
      (any_endpoint_before hAm hBm p hx hmiss)
  · change x = recordVertex w m at hx
    subst x
    exact p.start_mem_vertices

private def optimal {w : ℕ → Fin 3} (longest : Bool) {u v : PresentVertex w} (p : Path u v) : Prop :=
  if longest then IsLongest p else IsShortest p

private theorem optimal_prefix {w : ℕ → Fin 3} {longest : Bool} {u v z : PresentVertex w}
    {p : Path u v} {q : Path v z} (hp : optimal longest (p.comp q)) : optimal longest p := by
  cases longest
  · exact IsShortest.of_comp_left hp
  · exact IsLongest.of_comp_left hp

private theorem exists_infinite_of_prefixes {w : ℕ → Fin 3} (longest : Bool)
    (start : PresentVertex w) (v : ℕ → PresentVertex w)
    (Q : (k : ℕ) → Path start (v k))
    (hQ : ∀ k, optimal longest (Q k))
    (hext : ∀ k, ∃ r : Path (v k) (v (k + 1)), Q (k + 1) = (Q k).comp r)
    (hlen : ∀ k, k ≤ (Q k).length) :
    ∃ P : InfinitePresentPath w start, (∀ N, optimal longest (P.initial N).2) ∧
      ∀ k, pathEdgeList (Q k) = List.ofFn (fun i : Fin (Q k).length => P.edge i.val) := by
  classical
  have hmono {a b : ℕ} (hab : a ≤ b) : pathEdgeList (Q a) <+: pathEdgeList (Q b) := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨[], List.append_nil _⟩
    | succ b hab ih =>
      obtain ⟨r, hr⟩ := hext b
      apply ih.trans
      exact ⟨pathEdgeList r, (pathEdgeList_comp (Q b) r).symm.trans (congrArg pathEdgeList hr).symm⟩
  have hex (N : ℕ) : ∃ t : (z : PresentVertex w) × Path start z,
      ∃ r : Path t.1 (v N), Q N = t.2.comp r ∧ t.2.length = N := by
    obtain ⟨z, p, q, hp, hl⟩ := (Q N).exists_eq_comp_of_le_length (hlen N)
    exact ⟨⟨z, p⟩, q, hp, hl⟩
  choose t r hr htlen using hex
  have htpre (N : ℕ) : pathEdgeList (t N).2 <+: pathEdgeList (Q N) := by
    refine ⟨pathEdgeList (r N), ?_⟩
    rw [hr N, pathEdgeList_comp]
  let edge (i : ℕ) : ℕ := (pathEdgeList (Q (i + 1)))[i]'(by
    rw [pathEdgeList_length]
    have := hlen (i + 1)
    omega)
  have hedge (N : ℕ) : pathEdgeList (t N).2 = List.ofFn (fun i : Fin N => edge i.val) := by
    apply List.ext_getElem
    · simp only [pathEdgeList_length, htlen, List.length_ofFn]
    · intro i hi hj
      have hiN : i < N := by simpa only [List.length_ofFn] using hj
      rw [List.getElem_ofFn]
      change (pathEdgeList (t N).2)[i] = edge i
      dsimp only [edge]
      exact ((htpre N).getElem hi).trans
        ((hmono (by omega : i + 1 ≤ N)).getElem (by
          rw [pathEdgeList_length]
          have := hlen (i + 1)
          omega)).symm
  refine ⟨⟨edge, t, htlen, hedge⟩, ?_, ?_⟩
  · intro N
    have hopt := hQ N
    rw [hr N] at hopt
    exact optimal_prefix hopt
  · intro k
    apply List.ext_getElem
    · simp only [pathEdgeList_length, List.length_ofFn]
    · intro i hi hj
      rw [List.getElem_ofFn]
      change (pathEdgeList (Q k))[i] = edge i
      dsimp only [edge]
      have hlarge := hmono (Nat.le_max_right (i + 1) k)
      have hsmall := hmono (Nat.le_max_left (i + 1) k)
      exact (hlarge.getElem hi).trans (hsmall.getElem (by
        rw [pathEdgeList_length]
        have := hlen (i + 1)
        omega)).symm


private theorem recordPathPrefix_optimal (w : ℕ → Fin 3) (n : ℕ → ℕ) (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (longest : Bool)
    (p : (k : ℕ) → Path (recordVertex w (n k)) (recordVertex w (n (k + 1))))
    (hp : ∀ k, optimal longest (p k)) :
    ∀ k, optimal longest (recordPathPrefix n p k) := by
  intro k
  induction k with
  | zero =>
    cases longest
    · intro q
      exact Nat.zero_le _
    · intro q
      exact Nat.le_of_eq (presentVertex_acyclic w _ q)
  | succ k ih =>
    change optimal longest ((recordPathPrefix n p k).comp (p k))
    have hsep : ∀ q : Path (recordVertex w (n 0)) (recordVertex w (n (k + 1))),
        recordVertex w (n k) ∈ q.vertices := by
      intro q
      by_cases hk : k = 0
      · subst k
        exact q.start_mem_vertices
      · exact recordVertex_mem_path w (hn (Nat.pos_of_ne_zero hk)) (hn (by omega))
          (hA k) (hB k) (hA (k + 1)) q
    cases longest
    · exact IsShortest.comp_of_forall_mem_vertices ih (hp k) hsep
    · exact IsLongest.comp_of_forall_mem_vertices ih (hp k) hsep


private theorem optimal_segments {w : ℕ → Fin 3} {start : PresentVertex w}
    (longest : Bool) (P : InfinitePresentPath w start)
    (hP : ∀ N, optimal longest (P.initial N).2) :
    ∀ a b : ℕ, 1 ≤ a → a ≤ b → ∃ z, ∃ q : Path z (P.initial b).1,
      q.length = b + 1 - a ∧
      pathEdgeList q = (List.ofFn (fun i : Fin b => P.edge i.val)).drop (a - 1) ∧
      optimal longest q := by
  intro a b ha hab
  obtain ⟨z, p, q, hpq, hp⟩ := (P.initial b).2.exists_eq_comp_of_le_length
    (show a - 1 ≤ (P.initial b).2.length by rw [P.prefix_length]; omega)
  refine ⟨z, q, ?_, ?_, ?_⟩
  · have hlen := P.prefix_length b
    rw [hpq, Path.length_comp, hp] at hlen
    omega
  · rw [← P.prefix_edges b, hpq, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
    exact List.drop_left.symm
  · have hopt := hP b
    rw [hpq] at hopt
    cases longest
    · exact IsShortest.of_comp_right hopt
    · exact IsLongest.of_comp_right hopt


private theorem any_start_infinite_blocks (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (x : PresentVertex w) (hx : x ∈ recordBefore w (n 0) ∪ {recordVertex w (n 0)})
    (longest : Bool) (q : Path x (recordVertex w (n 0))) (hq : optimal longest q)
    (p : (k : ℕ) → Path (recordVertex w (n k)) (recordVertex w (n (k + 1))))
    (hp : ∀ k, optimal longest (p k)) :
    ∃ P : InfinitePresentPath w x, ∀ N, optimal longest (P.initial N).2 := by
  let Q (k : ℕ) := q.comp (recordPathPrefix n p k)
  have hopt (k : ℕ) : optimal longest (Q k) := by
    cases k with
    | zero => exact hq
    | succ k =>
      have hb := recordPathPrefix_optimal w n hn hA hB longest p hp (k + 1)
      have hsep := fun r => any_start_mem_record w
        (recordSequence_R_unbounded_any w n hn hA) (hn (by omega : 0 < k + 1))
        (hA 0) (hB 0) (hA (k + 1)) hx r
      cases longest
      · exact IsShortest.comp_of_forall_mem_vertices hq hb hsep
      · exact IsLongest.comp_of_forall_mem_vertices hq hb hsep
  have hlen : ∀ k, k ≤ (recordPathPrefix n p k).length := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hpos : 0 < (p k).length := by
        by_contra h
        have hz : (p k).length = 0 := by omega
        exact recordVertex_ne w (hn (by omega)) (hA (k + 1))
          ((p k).eq_of_length_zero hz)
      change k + 1 ≤ ((recordPathPrefix n p k).comp (p k)).length
      rw [Path.length_comp]
      omega
  obtain ⟨P, hP, _⟩ := exists_infinite_of_prefixes longest x
    (fun k => recordVertex w (n k)) Q hopt
    (fun k => ⟨p k, by simp only [Q, recordPathPrefix, Path.comp_assoc]⟩)
    (fun k => by dsimp only [Q]; rw [Path.length_comp]; exact (hlen k).trans (Nat.le_add_left _ _))
  exact ⟨P, hP⟩

/-- From any allocated vertex before the first of an increasing record
sequence, both infinite extremal present paths exist. All finite intervals
have the required optimality (`def-infinite-geo`, -/
theorem recordSequence_exists_infinite_extremal_any_start (w : ℕ → Fin 3)
    (n : ℕ → ℕ) (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j)
    (x : PresentVertex w) (halloc : ∃ m, x.id < (kmswStage w m).nextVertex)
    (hx : x ∈ recordBefore w (n 0) ∪ {recordVertex w (n 0)}) :
    (∃ P : InfinitePresentPath w x, P.HasLongestSegments) ∧
    (∃ P : InfinitePresentPath w x, P.HasShortestSegments) := by
  classical
  obtain ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩⟩ := allocated_exists_extremal_to_record w (n 0)
    (recordSequence_R_unbounded_any w n hn hA) (hA 0) (hB 0) x halloc hx
  have he (k : ℕ) := recordVertex_exists_extremal w (hn (by omega : k < k + 1))
    (hA k) (hA (k + 1)) (hB (k + 1))
  choose p hp using fun k => (he k).1
  choose q hq using fun k => (he k).2
  obtain ⟨P, hP⟩ := any_start_infinite_blocks w n hn hA hB x hx true p₀ hp₀ p hp
  obtain ⟨Q, hQ⟩ := any_start_infinite_blocks w n hn hA hB x hx false q₀ hq₀ q hq
  exact ⟨⟨P, optimal_segments true P hP⟩, ⟨Q, optimal_segments false Q hQ⟩⟩


/-- Every allocated vertex is on the finite old side of all sufficiently late -/
theorem allocated_eventually_before_records (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ t, R w t ≤ a) (x : PresentVertex w)
    (hx : ∃ t, x.id < (kmswStage w t).nextVertex) :
    ∃ N, ∀ n, N ≤ n → (∀ j < n, R w n ≤ R w j - 1) →
      x ∈ recordBefore w n := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨m, hm⟩ := allocated_vertex_eventually_activeInitial_of_R_unbounded w hR x.id ⟨t, ht⟩
  refine ⟨max t m + 1, fun n hn hA => ?_⟩
  have hmn : m < n := by omega
  refine ⟨ht.trans_le (CutConverse.nextVertex_mono w (by omega)), ?_, ?_⟩
  · change x.id ≠ (kmswStage w n).west (act w n)
    rw [← CutConverse.activeInitial_eq, ← hm]
    exact activeInitial_ne_of_right_record w n hA m hmn
  · intro heq
    have hne := activeEast_ne_activeInitial w (j := m) (n := n) hmn.le
    apply hne
    rw [hm]
    exact heq.symm

/-- An increasing record sequence has a tail whose first record is after an -/
theorem recordSequence_tail_before_allocated (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : StrictMono n)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (x : PresentVertex w) (hx : ∃ t, x.id < (kmswStage w t).nextVertex) :
    ∃ K, ∀ k, x ∈ recordBefore w (n (K + k)) := by
  obtain ⟨N, hN⟩ := allocated_eventually_before_records w
    (recordSequence_R_unbounded_any w n hn hA) x hx
  refine ⟨N, fun k => hN _ ?_ (hA (N + k))⟩
  exact (Nat.le_add_right N k).trans (hn.id_le (N + k))

/-- An infinite set of explicit records gives both infinite extremal present
paths simultaneously for every allocated start -/
theorem infinite_records_exists_allocated_infinite_extremal (w : ℕ → Fin 3)
    (hS : {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}.Infinite) :
    ∀ x : PresentVertex w, (∃ t, x.id < (kmswStage w t).nextVertex) →
      (∃ P : InfinitePresentPath w x, P.HasLongestSegments) ∧
      (∃ P : InfinitePresentPath w x, P.HasShortestSegments) := by
  let S : Set ℕ := {n | (∀ j < n, R w n ≤ R w j - 1) ∧
    ∀ j, n ≤ j → L w n ≤ L w j}
  let : Infinite S := hS.to_subtype
  let e : ℕ ≃o S := Nat.Subtype.orderIsoOfNat S
  let n : ℕ → ℕ := fun k => (e k).val
  have hn : StrictMono n := by
    intro a b hab
    exact e.strictMono hab
  have hA (k : ℕ) : ∀ j < n k, R w (n k) ≤ R w j - 1 := (e k).property.1
  have hB (k : ℕ) : ∀ j, n k ≤ j → L w (n k) ≤ L w j := (e k).property.2
  intro x hx
  obtain ⟨K, hK⟩ := recordSequence_tail_before_allocated w n hn hA x hx
  exact recordSequence_exists_infinite_extremal_any_start w (fun k => n (K + k))
    (fun a b hab => hn (Nat.add_lt_add_left hab K))
    (fun k => hA (K + k)) (fun k => hB (K + k)) x hx (Or.inl (hK 0))

/-- For the Pitman code of the shifted iid sequence, almost surely every
allocated vertex starts both an infinite longest-segment path and an infinite
shortest-segment path. The universal quantifier is inside the almost-sure event -/
theorem pitmanCodes_ae_exists_allocated_infinite_extremal :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ x : PresentVertex w, (∃ t, x.id < (kmswStage w t).nextVertex) →
        (∃ P : InfinitePresentPath w x, P.HasLongestSegments) ∧
        (∃ P : InfinitePresentPath w x, P.HasShortestSegments) := by
  filter_upwards [pitmanCodes_ae_infinite_cutSeparation_records] with ω hS
  exact infinite_records_exists_allocated_infinite_extremal _ hS

end DirectedDistances.KMSW
