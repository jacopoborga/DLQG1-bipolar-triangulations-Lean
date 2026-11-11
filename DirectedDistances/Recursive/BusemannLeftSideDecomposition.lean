module

public import DirectedDistances.KMSW.MhatPrimeVertexForward
public import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix
public import DirectedDistances.Recursive.BusemannMeasurable

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.

Root reachability is closed under directed continuation. Every path from its complement
into it splits at a first entry, with its suffix wholly in the reachable submap. The
path-length decomposition below uses the actual entry interface, retaining edge IDs.
The interface is identified with vertices of the geometric beta stream, using the
existing crossing-edge boundary-incidence theorem and beta boundary enumeration.

Excursions between visits to a longest geodesic can be replaced by its own segment
without changing an optimal total length. Full geometric side confinement and the
left Busemann formula remain the unassumed propositions at the end of this file.
Their side carriers must still be constructed and identified with the primed map
glued to the hatted left side; no such identification is supplied by the length formula. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The vertices of the induced root-reachable submap, on the raw KMSW carrier. -/
@[expose] def leftHatVertices (w : ℕ → Fin 3) : Set (PresentVertex w) :=
  {v | Reachable (⟨0⟩ : PresentVertex w) v}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The directed entry interface: a reachable vertex admitting an incoming present arrow -/
@[expose] def leftHatEntryVertices (w : ℕ → Fin 3) : Set (PresentVertex w) :=
  {v | v ∈ leftHatVertices w ∧
    ∃ u : PresentVertex w, u ∉ leftHatVertices w ∧ Nonempty (u ⟶ v)}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every directed continuation of a reachable vertex remains reachable. -/
theorem leftHatVertices_closed {w : ℕ → Fin 3} {x y : PresentVertex w}
    (hx : x ∈ leftHatVertices w) (p : Path x y) : y ∈ leftHatVertices w :=
  hx.trans p.reachable

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every vertex, including endpoints, of a path started in the hatted map stays in it. -/
theorem leftHatVertices_path_closed {w : ℕ → Fin 3} {x y : PresentVertex w}
    (hx : x ∈ leftHatVertices w) (p : Path x y) :
    ∀ v ∈ p.vertices, v ∈ leftHatVertices w := by
  intro v hv
  obtain ⟨a, _, _⟩ := p.exists_eq_comp_of_mem_vertices hv
  exact leftHatVertices_closed hx a

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every vertex on a path ending outside the hatted map is outside the hatted map. -/
private theorem leftOutside_path_closed_backwards {w : ℕ → Fin 3}
    {x y : PresentVertex w} (hy : y ∉ leftHatVertices w) (p : Path x y) :
    ∀ v ∈ p.vertices, v ∉ leftHatVertices w := by
  intro v hv hreach
  obtain ⟨_, b, _⟩ := p.exists_eq_comp_of_mem_vertices hv
  exact hy (leftHatVertices_closed hreach b)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
First-entry splitting retains the original arrow-valued path. The prefix has no hatted
vertex other than its final vertex; the suffix never leaves the hatted map. This is
proved before identifying the entry interface with beta. -/
theorem leftHat_firstEntry_split {w : ℕ → Fin 3} {x y : PresentVertex w}
    (p : Path x y) (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    ∃ v ∈ leftHatEntryVertices w, ∃ a : Path x v, ∃ b : Path v y,
      p = a.comp b ∧
      (∀ u ∈ a.vertices, u ≠ v → u ∉ leftHatVertices w) ∧
      (∀ u ∈ b.vertices, u ∈ leftHatVertices w) := by
  induction p with
  | nil => exact (hx hy).elim
  | @cons z y p e ih =>
    by_cases hz : z ∈ leftHatVertices w
    · obtain ⟨v, hv, a, b, hp, ha, hb⟩ := ih hz
      refine ⟨v, hv, a, b.cons e, ?_, ha, ?_⟩
      · rw [hp, Path.comp_cons]
      · intro u hu
        rcases (Path.mem_vertices_cons b e).mp hu with hu | hu
        · exact hb u hu
        · exact hu ▸ hy
    · refine ⟨y, ⟨hy, z, hz, ⟨e⟩⟩, p.cons e, Path.nil, ?_, ?_, ?_⟩
      · exact (Path.comp_nil _).symm
      · intro u hu hne
        rcases (Path.mem_vertices_cons p e).mp hu with hu | hu
        · exact leftOutside_path_closed_backwards hz p u hu
        · exact (hne hu).elim
      · intro u hu
        have heq : u = y := by simpa only [Path.vertices_nil, List.mem_singleton] using hu
        exact heq ▸ hy

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Lengths in the primed part with the entry vertex adjoined. Every other visited vertex
is outside the hatted map; missing edges are never directed arrows. -/
@[expose] def leftPrimedEntryLengths (w : ℕ → Fin 3) (x v : PresentVertex w) : Set ℕ :=
  {n | ∃ p : Path x v, p.length = n ∧
    ∀ u ∈ p.vertices, u ≠ v → u ∉ leftHatVertices w}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Lengths of paths wholly in the induced hatted map, using raw edge identities. -/
@[expose] def leftHatPathLengths (w : ℕ → Fin 3) (v y : PresentVertex w) : Set ℕ :=
  {n | ∃ p : Path v y, p.length = n ∧ ∀ u ∈ p.vertices, u ∈ leftHatVertices w}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
All attainable lengths decompose at the actual first-entry interface. Equality of
length sets also covers unreachable pairs and makes no boundedness assumption.
The beta-interface identification is proved below. -/
theorem leftHat_pathLengths_firstEntry {w : ℕ → Fin 3} {x y : PresentVertex w}
    (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    pathLengths x y = {n | ∃ v ∈ leftHatEntryVertices w,
      ∃ a ∈ leftPrimedEntryLengths w x v, ∃ b ∈ leftHatPathLengths w v y, n = a + b} := by
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨v, hv, a, b, hp, ha, hb⟩ := leftHat_firstEntry_split p hx hy
    exact ⟨v, hv, a.length, ⟨a, rfl, ha⟩, b.length, ⟨b, rfl, hb⟩,
      by simp only [hp, Path.length_comp]⟩
  · rintro ⟨v, _, a, ⟨p, hp, _⟩, b, ⟨q, hq, _⟩, rfl⟩
    exact ⟨p.comp q, by simp only [Path.length_comp, hp, hq]⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Interface identification: an arrow entering the hatted vertex set has
its head on the specified beta stream. No sign restriction is imposed on the raw walk.
This proposition is proved below and is not an additional premise. -/
@[expose] def LeftHatEntryOnBeta : Prop :=
  ∀ (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w),
    ∀ v ∈ leftHatEntryVertices w, ∃ t, v.id = kmswBeta0Vertices w hfin hb t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Each indexed beta vertex is the west endpoint of the corresponding beta-stream edge. -/
private theorem leftBetaVertex_tail (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) (t : ℕ) :
    kmswBeta0Vertices w hfin hb t = edgeWest w (kmswBeta0Stream w hfin hb t).1 := by
  cases t with
  | zero => exact (kmswBeta0Stream_start w hfin hb).symm
  | succ t => exact (kmswBeta0Stream_chain w hfin hb t).symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The actual first-entry interface lies on beta, using the proved geometric crossing -/
theorem leftHatEntryOnBeta_proved : LeftHatEntryOnBeta := by
  intro w hfin hb v hv
  obtain ⟨hv, u, hu, ⟨e⟩⟩ := hv
  have hnot : ¬ MhatGeometricEdge w e.val := by
    intro he
    apply hu
    have ht := he.1
    rw [e.property.2.1] at ht
    exact ht
  obtain ⟨f, hf, hfv⟩ := reachableEndpointCrossingWestBoundaryGoal_holds w hfin hb
    e.val v.id hnot hv (Or.inr e.property.2.2)
  obtain ⟨t, ht⟩ := beta0_westBoundary_reached w hfin hb f hf
  rcases hfv with hfv | hfv
  · refine ⟨t, ?_⟩
    rw [leftBetaVertex_tail, ht]
    exact hfv.symm
  · refine ⟨t + 1, ?_⟩
    change v.id = edgeEast w (kmswBeta0Stream w hfin hb t).1
    rw [ht]
    exact hfv.symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A path from outside the hatted map to inside first enters at beta and never leaves.
Both factors are genuine paths on the raw carrier with their original edge IDs. -/
theorem leftHat_firstEntry_beta (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) {x y : PresentVertex w}
    (p : Path x y) (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    ∃ t, ∃ a : Path x ⟨kmswBeta0Vertices w hfin hb t⟩,
      ∃ b : Path (⟨kmswBeta0Vertices w hfin hb t⟩ : PresentVertex w) y,
      p = a.comp b ∧
      (∀ u ∈ a.vertices, u.id ≠ kmswBeta0Vertices w hfin hb t →
        u ∉ leftHatVertices w) ∧
      (∀ u ∈ b.vertices, u ∈ leftHatVertices w) := by
  obtain ⟨v, hv, a, b, hp, ha, hb'⟩ := leftHat_firstEntry_split p hx hy
  obtain ⟨t, ht⟩ := leftHatEntryOnBeta_proved w hfin hb v hv
  have heq : v = (⟨kmswBeta0Vertices w hfin hb t⟩ : PresentVertex w) := by
    cases v
    exact congrArg PresentVertex.mk ht
  subst v
  exact ⟨t, a, b, hp, fun u hu hne => ha u hu
    (fun h => hne (congrArg PresentVertex.id h)), hb'⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Exact beta-indexed decomposition of all path lengths; in particular, taking the
supremum of these lengths gives the longest distance without a finite-distance
subtraction or an unreachable-as-zero convention. -/
theorem leftHat_pathLengths_beta (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) {x y : PresentVertex w}
    (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    pathLengths x y = {n | ∃ t,
      ∃ a ∈ leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb t⟩,
      ∃ b ∈ leftHatPathLengths w ⟨kmswBeta0Vertices w hfin hb t⟩ y, n = a + b} := by
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨v, hv, a, b, hp, ha, hb'⟩ := leftHat_firstEntry_split p hx hy
    obtain ⟨t, ht⟩ := leftHatEntryOnBeta_proved w hfin hb v hv
    have heq : v = (⟨kmswBeta0Vertices w hfin hb t⟩ : PresentVertex w) := by
      cases v
      exact congrArg PresentVertex.mk ht
    subst v
    exact ⟨t, a.length, ⟨a, rfl, ha⟩, b.length, ⟨b, rfl, hb'⟩,
      by simp only [hp, Path.length_comp]⟩
  · rintro ⟨t, a, ⟨p, hp, _⟩, b, ⟨q, hq, _⟩, rfl⟩
    exact ⟨p.comp q, by simp only [Path.length_comp, hp, hq]⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Supremum of a restricted length set, with bottom for the empty set. Applications
below prove boundedness from finite incidence before identifying this with LDP. -/
@[expose] noncomputable def leftLengthSup (s : Set ℕ) : WithBot ℕ :=
  sSup ((fun n : ℕ => (n : WithBot ℕ)) '' s)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
If n is the greatest element of s, the supremum of its coerced lengths is n. -/
private theorem leftLengthSup_eq (s : Set ℕ) {n : ℕ} (hn : IsGreatest s n) :
    leftLengthSup s = (n : WithBot ℕ) := by
  have hm : (n : WithBot ℕ) ∈ (fun k : ℕ => (k : WithBot ℕ)) '' s :=
    ⟨n, hn.1, rfl⟩
  have hu : ∀ z ∈ (fun k : ℕ => (k : WithBot ℕ)) '' s, z ≤ (n : WithBot ℕ) := by
    rintro z ⟨k, hk, rfl⟩
    exact WithBot.coe_le_coe.mpr (hn.2 hk)
  exact le_antisymm (csSup_le ⟨_, hm⟩ hu) (le_csSup ⟨_, hu⟩ hm)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
For finite a and b, if every i + j is at most N, their suprema sum to at most N. -/
private theorem leftLengthSup_add_le (a b : Set ℕ) (ha : a.Finite) (hb : b.Finite)
    (N : ℕ) (hN : ∀ i ∈ a, ∀ j ∈ b, i + j ≤ N) :
    leftLengthSup a + leftLengthSup b ≤ (N : WithBot ℕ) := by
  classical
  by_cases hna : a.Nonempty
  · by_cases hnb : b.Nonempty
    · have hma : IsGreatest a (sSup a) :=
        ⟨hna.csSup_mem ha, fun _ hi => le_csSup ha.bddAbove hi⟩
      have hmb : IsGreatest b (sSup b) :=
        ⟨hnb.csSup_mem hb, fun _ hj => le_csSup hb.bddAbove hj⟩
      rw [leftLengthSup_eq a hma, leftLengthSup_eq b hmb]
      change ((sSup a + sSup b : ℕ) : WithBot ℕ) ≤ (N : WithBot ℕ)
      exact WithBot.coe_le_coe.mpr (hN _ hma.1 _ hmb.1)
    · have he : b = ∅ := Set.not_nonempty_iff_eq_empty.mp hnb
      simp only [he, leftLengthSup, Set.image_empty, csSup_empty, WithBot.add_bot, bot_le]
  · have he : a = ∅ := Set.not_nonempty_iff_eq_empty.mp hna
    simp only [he, leftLengthSup, Set.image_empty, csSup_empty, WithBot.bot_add, bot_le]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite incidence bounds lengths of paths to v whose other vertices lie outside the hatted map. -/
private theorem leftPrimedEntryLengths_finite (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (x v : PresentVertex w) : (leftPrimedEntryLengths w x v).Finite := by
  apply (pathLengths_finite_of_bddAbove (present_pathLengths_bddAbove w hfin x v)).subset
  rintro n ⟨p, hp, _⟩
  exact ⟨p, hp⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite incidence bounds lengths of paths from v to y wholly in the hatted map. -/
private theorem leftHatPathLengths_finite (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v y : PresentVertex w) : (leftHatPathLengths w v y).Finite := by
  apply (pathLengths_finite_of_bddAbove (present_pathLengths_bddAbove w hfin v y)).subset
  rintro n ⟨p, hp, _⟩
  exact ⟨p, hp⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The longest-distance first-entry formula, as a supremum over beta vertices of the
sum of the primed-entry and hatted distances. Finite incidence bounds every distance
involved; an unreachable summand is bottom and the sum preserves bottom. -/
theorem leftHat_ldp_beta (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) {x y : PresentVertex w}
    (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    ldpSup x y = ⨆ t : ℕ,
      leftLengthSup (leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb t⟩) +
      leftLengthSup (leftHatPathLengths w ⟨kmswBeta0Vertices w hfin hb t⟩ y) := by
  classical
  by_cases hr : Reachable x y
  · obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove
      (present_pathLengths_bddAbove w hfin x y) hr
    have hmax : IsGreatest (pathLengths x y) p.length := by
      refine ⟨⟨p, rfl⟩, ?_⟩
      rintro n ⟨q, rfl⟩
      exact hp q
    have hfull : ldpSup x y = (p.length : WithBot ℕ) := leftLengthSup_eq _ hmax
    rw [hfull]
    have hupper (t : ℕ) :
        leftLengthSup (leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb t⟩) +
        leftLengthSup (leftHatPathLengths w ⟨kmswBeta0Vertices w hfin hb t⟩ y) ≤
          (p.length : WithBot ℕ) := by
      apply leftLengthSup_add_le _ _ (leftPrimedEntryLengths_finite w hfin _ _)
        (leftHatPathLengths_finite w hfin _ _) p.length
      rintro i ⟨a, ha, _⟩ j ⟨b, hb', _⟩
      have h := hp (a.comp b)
      simpa only [Path.length_comp, ha, hb'] using h
    apply le_antisymm
    · obtain ⟨v, hv, a, b, hsplit, ha, hb'⟩ := leftHat_firstEntry_split p hx hy
      obtain ⟨t, ht⟩ := leftHatEntryOnBeta_proved w hfin hb v hv
      have heq : v = (⟨kmswBeta0Vertices w hfin hb t⟩ : PresentVertex w) := by
        cases v
        exact congrArg PresentVertex.mk ht
      subst v
      have hma : IsGreatest (leftPrimedEntryLengths w x
          ⟨kmswBeta0Vertices w hfin hb t⟩) a.length := by
        refine ⟨⟨a, rfl, ha⟩, ?_⟩
        rintro n ⟨q, rfl, _⟩
        have hh : IsLongest (a.comp b) := hsplit ▸ hp
        exact hh.of_comp_left q
      have hmb : IsGreatest (leftHatPathLengths w
          ⟨kmswBeta0Vertices w hfin hb t⟩ y) b.length := by
        refine ⟨⟨b, rfl, hb'⟩, ?_⟩
        rintro n ⟨q, rfl, _⟩
        have hh : IsLongest (a.comp b) := hsplit ▸ hp
        exact hh.of_comp_right q
      apply le_ciSup_of_le ⟨_, by rintro z ⟨k, rfl⟩; exact hupper k⟩ t
      rw [leftLengthSup_eq _ hma, leftLengthSup_eq _ hmb]
      change (p.length : WithBot ℕ) ≤ ((a.length + b.length : ℕ) : WithBot ℕ)
      exact le_of_eq (congrArg (fun n : ℕ => (n : WithBot ℕ))
        (by rw [hsplit, Path.length_comp]))
    · exact ciSup_le hupper
  · rw [ldpSup_eq_bot_of_not_reachable hr]
    apply le_antisymm bot_le
    apply ciSup_le
    intro t
    have hempty : leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb t⟩ = ∅ ∨
        leftHatPathLengths w ⟨kmswBeta0Vertices w hfin hb t⟩ y = ∅ := by
      by_cases ha : (leftPrimedEntryLengths w x
          ⟨kmswBeta0Vertices w hfin hb t⟩).Nonempty
      · obtain ⟨i, a, _, _⟩ := ha
        right
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro j ⟨b, _, _⟩
        exact hr ⟨a.comp b⟩
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp ha)
    rcases hempty with he | he <;>
      simp only [he, leftLengthSup, Set.image_empty, csSup_empty, WithBot.bot_add, WithBot.add_bot,
        le_refl]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An excursion between visits to a longest geodesic can be replaced by the intervening
geodesic segment. For an already longest whole path, the replacement has exactly the
same length and remains longest. No geometric side confinement is asserted here. -/
theorem leftGeodesic_replace_excursion {w : ℕ → Fin 3}
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasLongestSegments)
    (i j : ℕ) {x y : PresentVertex w}
    (a : Path x (P.initial i).1) (b : Path (P.initial i).1 (P.initial j).1)
    (c : Path (P.initial j).1 y) (hp : IsLongest ((a.comp b).comp c)) :
    ∃ s : Path (P.initial i).1 (P.initial j).1,
      i ≤ j ∧ s.length = j - i ∧
      pathEdgeList s = List.ofFn (fun k : Fin (j - i) => P.edge (i + k.val)) ∧
      s.length = b.length ∧ IsLongest ((a.comp s).comp c) := by
  have hij : i ≤ j := by
    by_contra hn
    have hji : j ≤ i := by omega
    have H := P.exists_shift_split j (i - j)
    rw [Nat.add_sub_of_le hji] at H
    obtain ⟨_, r, _, _, hr, _⟩ := H
    have hz := presentVertex_acyclic w _ (r.comp b)
    rw [Path.length_comp, hr] at hz
    omega
  have H := P.exists_shift_split i (j - i)
  rw [Nat.add_sub_of_le hij] at H
  obtain ⟨r, s, heq, _, hslen, hsedge⟩ := H
  have hlong := P.initial_isLongest w hP j
  rw [heq] at hlong
  have hle : b.length ≤ s.length := hlong.of_comp_right b
  have he : s.length = b.length :=
    le_antisymm (hp.of_comp_middle s) hle
  refine ⟨s, hij, hslen, hsedge, he, ?_⟩
  apply hp.of_length_eq
  simp only [Path.length_comp, he]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every geodesic prefix has attained finite root distance exactly equal to its index, -/
theorem leftGeodesic_root_distance {w : ℕ → Fin 3}
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasLongestSegments) (t : ℕ) :
    presentLdp (⟨0⟩ : PresentVertex w) (P.initial t).1 =
      ((t : ℕ∞) : WithBot ℕ∞) := by
  rw [presentLdp_eq_length (P.initial_isLongest w hP t), P.prefix_length]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Attainable lengths in a specified closed-side edge carrier. The carrier is explicit:
this definition does not identify a candidate carrier with the paper's geometric side. -/
@[expose] def leftClosedSidePathLengths (w : ℕ → Fin 3) (closedLeftEdges : Set ℕ)
    (x y : PresentVertex w) : Set ℕ :=
  {n | ∃ p : Path x y, p.length = n ∧ ∀ e ∈ pathEdgeList p, e ∈ closedLeftEdges}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The remaining geometric exchange obligation, parameterized by the actual closed-side
vertex and edge carriers so their construction and identification are not hidden.
A longest path from the left side to the right side admits one seam split, with its
prefix in the closed left side and suffix in the closed right side. The suffix
cannot revisit the seam: its only seam vertex is its start. This proposition is open;
no theorem in this file assumes it. Excursion replacement alone is proved above.
Intended instantiation: P is the raw leftmost LDP geodesic from x_0 (see
`Recursive/BusemannLeftAlongGeodesic.lean`); the Prop is not claimed for arbitrary P. -/
@[expose] def LeftClosedSideGeodesicExchange (w : ℕ → Fin 3)
    (P : InfinitePresentPath w ⟨0⟩)
    (closedLeftVertices closedRightVertices : Set (PresentVertex w))
    (closedLeftEdges closedRightEdges : Set ℕ) : Prop :=
  ∀ x ∈ closedLeftVertices, ∀ y ∈ closedRightVertices,
    ∀ p : Path x y, IsLongest p →
      ∃ t, ∃ a : Path x (P.initial t).1, ∃ b : Path (P.initial t).1 y,
        a.length + b.length = p.length ∧ IsLongest (a.comp b) ∧
        (∀ e ∈ pathEdgeList a, e ∈ closedLeftEdges) ∧
        (∀ e ∈ pathEdgeList b, e ∈ closedRightEdges) ∧
        ∀ s, (P.initial s).1 ∈ b.vertices → s = t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The precise remaining left-profile formula at a specified geometric closed-left
carrier and raw geodesic. For each positive `j`, sufficiently late right-boundary
target differences equal one integer `c`; sufficiently late seam targets have an
attained finite closed-left maximum `n` with `n - t = c`. Root-to-seam distance is
explicitly finite and equal to `t`. The same `c` is the measurable profile value.
The formula is open, not assumed. Instantiating the carrier with the primed map glued
to the hatted closed left side still requires its geometric identification.
Intended instantiation: P is the raw leftmost LDP geodesic from x_0 (see
`Recursive/BusemannLeftAlongGeodesic.lean`); the Prop is not claimed for arbitrary P. -/
@[expose] def LeftBusemannAlongGeodesic (ω : ℕ → Fin 3)
    (P : InfinitePresentPath (fun i => ω (i + 1)) ⟨0⟩)
    (closedLeftEdges : Set ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∃ c : ℤ,
    busemannLDPMeasurableVersion ω (-(j : ℤ)) = c ∧
    (∀ᶠ m in Filter.atTop, boundaryLdpDifference ω (-(j : ℤ)) m = c) ∧
    ∀ᶠ t in Filter.atTop, ∃ n : ℕ,
      IsGreatest (leftClosedSidePathLengths (fun i => ω (i + 1)) closedLeftEdges
        ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩ (P.initial t).1) n ∧
      presentLdp (⟨0⟩ : PresentVertex (fun i => ω (i + 1))) (P.initial t).1 =
        ((t : ℕ∞) : WithBot ℕ∞) ∧ (n : ℤ) - (t : ℤ) = c

end DirectedDistances.Recursive
