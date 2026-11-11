module

public import DirectedDistances.KMSW.GluingBoundaryOrder
public import DirectedDistances.KMSW.PrimedLimitRotation
public import DirectedDistances.KMSW.KMSWMeasurability
public import DirectedDistances.KMSW.FutureMapHatLaw
public import DirectedDistances.Recursive.BusemannLeftSideDecomposition
import DirectedDistances.KMSW.PrimedReachabilityUnion

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk Quiver MeasureTheory Filter

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Stage presence uses the C18 missing-root state, including every other missing tag. -/
@[expose] def primedEntryStagePresent (u : ℕ → Fin 3) (n e : ℕ) : Prop :=
  e < (kmswMissingRootStage u n).nextEdge ∧
    (kmswMissingRootStage u n).present e = true

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Precisely the ordinary stage arrows other than the retained missing root are allowed. -/
theorem primedEntryStagePresent_iff (u : ℕ → Fin 3) (n e : ℕ) :
    primedEntryStagePresent u n e ↔ e ≠ 0 ∧
      e < (kmswStage u n).nextEdge ∧ (kmswStage u n).present e = true := by
  have ha := kmswMissingRootStage_agree u n
  constructor
  · rintro ⟨he, hp⟩
    have hz : e ≠ 0 := by
      rintro rfl
      rw [kmswMissingRootStage_present_zero] at hp
      cases hp
    exact ⟨hz, ha.2.1 ▸ he, (ha.2.2.2.2.1 e hz).symm.trans hp⟩
  · rintro ⟨hz, he, hp⟩
    exact ⟨ha.2.1.symm ▸ he, (ha.2.2.2.2.1 e hz).trans hp⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The stage predicate recovers exactly the existing primed limit presence convention. -/
theorem primedEntryStagePresent_limit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (e : ℕ) :
    (∃ n, primedEntryStagePresent (primedCode (primedSimInput w) h) n e) ↔
      PrimedEdgePresent w h e := Iff.rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Absence at all local stages is exactly the H' missing-edge tag. -/
theorem primedEntryStagePresent_missing (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (e : ℕ) :
    (¬ ∃ n, primedEntryStagePresent (primedCode (primedSimInput w) h) n e) ↔
      primeMissingEdge w hfin hb (primedLimitEdgeMap w h e) :=
  primedLimitEdgeMap_missing w h hfin hb e

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A state-indexed vertex ID; the quiver below retains geometric edge identities. -/
structure PrimedEntryVertex (s : State) where
  id : ℕ
  deriving DecidableEq

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Only allocated present edges of the supplied state are directed arrows. -/
instance primedEntryQuiver (s : State) : Quiver (PrimedEntryVertex s) where
  Hom a b := {e : ℕ // e < s.nextEdge ∧ s.present e = true ∧
    s.west e = a.id ∧ s.east e = b.id}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The missing-root stage embeds in the ordinary limit by preserving vertex and edge IDs. -/
@[expose] def primedEntryStageToLimit (u : ℕ → Fin 3) (n : ℕ) :
    Prefunctor (PrimedEntryVertex (kmswMissingRootStage u n)) (PresentVertex u) where
  obj a := ⟨a.id⟩
  map {_ _} e := by
    have he := (primedEntryStagePresent_iff u n e.val).mp
      ⟨e.property.1, e.property.2.1⟩
    have ha := kmswMissingRootStage_agree u n
    exact ⟨e.val, ⟨n, he.2.1, he.2.2⟩,
      (edge_endpoints_eq u he.2.1).1.symm.trans
        ((ha.2.2.1 e.val).symm.trans e.property.2.2.1),
      (edge_endpoints_eq u he.2.1).2.symm.trans
        ((ha.2.2.2.1 e.val).symm.trans e.property.2.2.2)⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Embedding a primed stage path preserves its length. -/
theorem primedEntryStageToLimit_length (u : ℕ → Fin 3) (n : ℕ)
    {a b : PrimedEntryVertex (kmswMissingRootStage u n)} (p : Path a b) :
    ((primedEntryStageToLimit u n).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Deleting the root and all missing edges preserves literal path acyclicity. -/
theorem primedEntryStage_acyclic (u : ℕ → Fin 3) (n : ℕ) :
    acyclic (PrimedEntryVertex (kmswMissingRootStage u n)) := by
  intro a p
  rw [← primedEntryStageToLimit_length u n p]
  exact presentVertex_acyclic u _ _

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every vertex after the starting vertex of a stage path is allocated. -/
private theorem primedEntryStage_path_vertices (u : ℕ → Fin 3) (n : ℕ)
    {a b : PrimedEntryVertex (kmswMissingRootStage u n)} (p : Path a b) :
    ∀ v ∈ p.vertices, v = a ∨ v.id < (kmswMissingRootStage u n).nextVertex := by
  induction p with
  | nil =>
    intro v hv
    exact Or.inl (List.mem_singleton.mp hv)
  | @cons b c p e ih =>
    intro v hv
    rcases (Path.mem_vertices_cons p e).mp hv with hv | hv
    · exact ih v hv
    · subst v
      right
      have he := (primedEntryStagePresent_iff u n e.val).mp
        ⟨e.property.1, e.property.2.1⟩
      have hb := (kmswStage_endpoints_lt_nextVertex u n e.val he.2.1).2
      have ha := kmswMissingRootStage_agree u n
      rw [← ha.1, ← ha.2.2.2.1 e.val, e.property.2.2.2] at hb
      exact hb

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite-stage path lengths are bounded before any natural-valued supremum is used. -/
theorem primedEntryStage_lengths_bddAbove (u : ℕ → Fin 3) (n a b : ℕ) :
    BddAbove (pathLengths (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩) := by
  let s := kmswMissingRootStage u n
  let vs : Set (PrimedEntryVertex s) :=
    insert ⟨a⟩ (PrimedEntryVertex.mk '' Set.Iio s.nextVertex)
  apply pathLengths_bddAbove_of_finite_vertex_confinement (primedEntryStage_acyclic u n)
    vs ((Set.finite_Iio s.nextVertex).image PrimedEntryVertex.mk |>.insert ⟨a⟩)
  intro p v hv
  rcases primedEntryStage_path_vertices u n p v hv with hv | hv
  · exact Set.mem_insert_iff.mpr (Or.inl hv)
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨v.id, hv, by cases v; rfl⟩)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Finite-stage longest distance. `WithBot ℕ` is the option carrier: bottom is unreachable. -/
@[expose] noncomputable def primedEntryStageDistance (u : ℕ → Fin 3) (n a b : ℕ) :
    WithBot ℕ :=
  leftLengthSup (pathLengths (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The stage distance is bottom exactly for unreachable pairs, including no zero fallback. -/
theorem primedEntryStageDistance_eq_bot_iff (u : ℕ → Fin 3) (n a b : ℕ) :
    primedEntryStageDistance u n a b = ⊥ ↔
      ¬ Reachable (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩ := by
  constructor
  · intro hd ⟨p⟩
    have hb := primedEntryStage_lengths_bddAbove u n a b
    have himg : BddAbove ((fun k : ℕ => (k : WithBot ℕ)) ''
        pathLengths (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩) := by
      obtain ⟨N, hN⟩ := hb
      exact ⟨(N : WithBot ℕ), by
        rintro _ ⟨k, hk, rfl⟩
        exact WithBot.coe_le_coe.mpr (hN hk)⟩
    have hp : (p.length : WithBot ℕ) ≤ primedEntryStageDistance u n a b :=
      le_csSup himg ⟨p.length, ⟨p, rfl⟩, rfl⟩
    rw [hd] at hp
    exact WithBot.coe_ne_bot (le_bot_iff.mp hp)
  · intro hn
    exact ldpSup_eq_bot_of_not_reachable hn

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The inclusion from one primed stage to a later one keeps every edge identity. -/
@[expose] def primedEntryStageToLater (u : ℕ → Fin 3) (m n : ℕ) (hmn : m ≤ n) :
    Prefunctor (PrimedEntryVertex (kmswMissingRootStage u m))
      (PrimedEntryVertex (kmswMissingRootStage u n)) where
  obj a := ⟨a.id⟩
  map {_ _} e := by
    have he := (primedEntryStagePresent_iff u m e.val).mp
      ⟨e.property.1, e.property.2.1⟩
    have hn := present_mono u he.2.1 he.2.2 n hmn
    have hp := (primedEntryStagePresent_iff u n e.val).mpr ⟨he.1, hn⟩
    have ha := kmswMissingRootStage_agree u m
    have hb := kmswMissingRootStage_agree u n
    have ht := present_endpoints_stable u he.2.1 he.2.2 hmn
    exact ⟨e.val, hp.1, hp.2,
      (hb.2.2.1 e.val).trans (ht.1.trans
        ((ha.2.2.1 e.val).symm.trans e.property.2.2.1)),
      (hb.2.2.2.1 e.val).trans (ht.2.trans
        ((ha.2.2.2.1 e.val).symm.trans e.property.2.2.2))⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Passing to a later primed stage preserves path length. -/
theorem primedEntryStageToLater_length (u : ℕ → Fin 3) (m n : ℕ) (hmn : m ≤ n)
    {a b : PrimedEntryVertex (kmswMissingRootStage u m)} (p : Path a b) :
    ((primedEntryStageToLater u m n hmn).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Attainable length sets increase with the stage. -/
theorem primedEntryStage_lengths_mono (u : ℕ → Fin 3) (a b : ℕ) {m n : ℕ}
    (hmn : m ≤ n) :
    pathLengths (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u m)) ⟨b⟩ ⊆
      pathLengths (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩ := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(primedEntryStageToLater u m n hmn).mapPath p,
    primedEntryStageToLater_length u m n hmn p⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Under geometric finite incidence, even the union of all primed stage length sets is finite. -/
theorem primedEntryStage_lengths_union_finite (u : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence u) (a b : ℕ) :
    (⋃ n : ℕ, pathLengths
      (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩).Finite := by
  apply (pathLengths_finite_of_bddAbove
    (present_pathLengths_bddAbove u hfin ⟨a⟩ ⟨b⟩)).subset
  intro k hk
  obtain ⟨n, p, hp⟩ := Set.mem_iUnion.mp hk
  exact ⟨(primedEntryStageToLimit u n).mapPath p,
    (primedEntryStageToLimit_length u n p).trans hp⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Fixed-endpoint stage distances stabilize under finite incidence. The eventual
value is exactly the supremum of the union, with bottom when every stage is unreachable. -/
theorem primedEntryStageDistance_eventually (u : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence u) (a b : ℕ) :
    ∀ᶠ n in atTop, primedEntryStageDistance u n a b =
      leftLengthSup (⋃ m : ℕ, pathLengths
        (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u m)) ⟨b⟩) := by
  let S := ⋃ m : ℕ, pathLengths
    (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u m)) ⟨b⟩
  have hfinS : S.Finite := primedEntryStage_lengths_union_finite u hfin a b
  by_cases hne : S.Nonempty
  · have hmax := hne.isGreatest_csSup hfinS
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hmax.1
    filter_upwards [eventually_ge_atTop N] with n hn
    have hstage : IsGreatest
        (pathLengths (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩)
        (sSup S) :=
      ⟨primedEntryStage_lengths_mono u a b hn hN,
        fun _ hk => hmax.2 (Set.mem_iUnion.mpr ⟨n, hk⟩)⟩
    have hsup (T : Set ℕ) (hT : IsGreatest T (sSup S)) :
        leftLengthSup T = ((sSup S : ℕ) : WithBot ℕ) := by
      apply IsGreatest.csSup_eq
      exact ⟨⟨sSup S, hT.1, rfl⟩, by
        rintro _ ⟨k, hk, rfl⟩
        exact WithBot.coe_le_coe.mpr (hT.2 hk)⟩
    exact (hsup _ hstage).trans (hsup S hmax).symm
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    filter_upwards [] with n
    have hn : pathLengths
        (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hm : k ∈ S := Set.mem_iUnion.mpr ⟨n, hk⟩
      rw [he] at hm
      exact hm
    change leftLengthSup _ = leftLengthSup S
    rw [hn, he]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Outer vertices follow the raw west boundary: east root, west root, then the west
endpoints of `LL.reverse`. Thus index zero includes the beta start; the retained
root is the first geometric west edge. The ambient index is `-(j : ℤ)`.
The H' identification of this ordering is a separate unassumed Prop below. -/
@[expose] def primedEntryOuterVertex (s : State) (j : ℕ) : Option ℕ :=
  ([s.east 0, s.west 0] ++ s.LL.reverse.map s.west)[j]?

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Glue vertices are the east endpoints of `UR.reverse`, indexed from its bottom.
The local east endpoint is the ambient beta tail because the missing C13 side
has the reversed geometric endpoint order. No directed orientation is put on it. -/
@[expose] def primedEntryGlueVertex (s : State) (k : ℕ) : Option ℕ :=
  s.UR.reverse[k]?.map s.east

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The proved UR ordering gives the exact same beta edge index, without an R record. -/
theorem primedEntryGlueVertex_same_index (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (k n : ℕ)
    (hn : primedIntervalBase (primedSimInput w) h k + 1 ≤ n) :
    primedEntryGlueVertex (kmswStage (primedCode (primedSimInput w) h) n) k =
      some ((kmswStage (primedCode (primedSimInput w) h) n).east
        (primedBeta0EdgeIndex w h hfin hb hfin k)) := by
  unfold primedEntryGlueVertex
  rw [primedBeta0EdgeIndex_UR_reverse_order w h hfin hb hfin k n hn]
  rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Distance from outer index j to glue index k using only primed stage arrows.
An endpoint not yet in its boundary list has bottom distance at that stage. -/
@[expose] noncomputable def primedEntryBoundaryStageDistance
    (u : ℕ → Fin 3) (n j k : ℕ) : WithBot ℕ :=
  match primedEntryOuterVertex (kmswStage u n) j,
      primedEntryGlueVertex (kmswStage u n) k with
  | some a, some b => primedEntryStageDistance u n a b
  | _, _ => ⊥

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The missing-root state depends on exactly the same finite prefix as the ordinary state. -/
private theorem primedEntryMissingRoot_congr {u v : ℕ → Fin 3} {n : ℕ}
    (h : ∀ i < n, u i = v i) : kmswMissingRootStage u n = kmswMissingRootStage v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change kmswStep (kmswMissingRootStage u n) (u n) =
      kmswStep (kmswMissingRootStage v n) (v n)
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every fixed boundary stage distance is measurable in the entire primed code alone. -/
theorem measurable_primedEntryBoundaryStageDistance (n j k : ℕ) :
    @Measurable (ℕ → Fin 3) (WithBot ℕ) _ ⊤
      (fun u => primedEntryBoundaryStageDistance u n j k) := by
  let : MeasurableSpace (WithBot ℕ) := ⊤
  refine measurable_of_factors_prefix n _ (fun u v h => ?_)
  unfold primedEntryBoundaryStageDistance primedEntryStageDistance
  rw [kmswStage_congr h, primedEntryMissingRoot_congr h]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An eventual value, with none for failure to stabilize and some bottom for eventual
unreachability. The two cases are distinct; no natural zero default is used. -/
@[expose] noncomputable def primedEntryEventualValue (f : ℕ → WithBot ℕ) :
    Option (WithBot ℕ) := by
  classical
  exact if h : ∃ d, ∀ᶠ n in atTop, f n = d then some h.choose else none

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The eventual-value operation has its full characterization, including bottom. -/
theorem primedEntryEventualValue_eq_some_iff (f : ℕ → WithBot ℕ) (d : WithBot ℕ) :
    primedEntryEventualValue f = some d ↔ ∀ᶠ n in atTop, f n = d := by
  classical
  unfold primedEntryEventualValue
  split_ifs with h
  · constructor
    · intro he
      exact h.choose_spec.mono (fun n hn => hn.trans (Option.some.inj he))
    · intro hd
      obtain ⟨n, hn, hn'⟩ := (h.choose_spec.and hd).exists
      exact congrArg some (hn.symm.trans hn')
  · constructor
    · intro he
      cases he
    · intro hd
      exact (h ⟨d, hd⟩).elim

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Boundary code value after stabilization, with stabilization failure kept explicit. -/
@[expose] noncomputable def primedEntryDistanceCode (u : ℕ → Fin 3) (j k : ℕ) :
    Option (WithBot ℕ) :=
  primedEntryEventualValue (fun n => primedEntryBoundaryStageDistance u n j k)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The code reports some d exactly when the boundary stage distances stabilize at d. -/
theorem primedEntryDistanceCode_eq_some_iff (u : ℕ → Fin 3) (j k : ℕ)
    (d : WithBot ℕ) :
    primedEntryDistanceCode u j k = some d ↔
      ∀ᶠ n in atTop, primedEntryBoundaryStageDistance u n j k = d :=
  primedEntryEventualValue_eq_some_iff _ d

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
None means precisely failure to stabilize, distinct from some bottom for unreachability. -/
theorem primedEntryDistanceCode_eq_none_iff (u : ℕ → Fin 3) (j k : ℕ) :
    primedEntryDistanceCode u j k = none ↔
      ¬ ∃ d, ∀ᶠ n in atTop, primedEntryBoundaryStageDistance u n j k = d := by
  classical
  unfold primedEntryDistanceCode primedEntryEventualValue
  split_ifs <;> simp_all

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Each eventual constant event is measurable by a countable union of intersections. -/
private theorem measurableSet_primedEntry_eventually (j k : ℕ) (d : WithBot ℕ) :
    MeasurableSet {u | ∀ᶠ n in atTop, primedEntryBoundaryStageDistance u n j k = d} := by
  let : MeasurableSpace (WithBot ℕ) := ⊤
  have he : {u | ∀ᶠ n in atTop, primedEntryBoundaryStageDistance u n j k = d} =
      ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n),
        {u | primedEntryBoundaryStageDistance u n j k = d} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_atTop]
  rw [he]
  exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n =>
    MeasurableSet.iInter (fun _ => measurableSet_eq_fun
      (measurable_primedEntryBoundaryStageDistance n j k) measurable_const)))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Measurability includes stabilization failure and unreachable distance values. -/
theorem measurable_primedEntryDistanceCode (j k : ℕ) :
    @Measurable (ℕ → Fin 3) (Option (WithBot ℕ)) _ ⊤
      (fun u => primedEntryDistanceCode u j k) := by
  let : MeasurableSpace (Option (WithBot ℕ)) := ⊤
  classical
  refine measurable_to_countable' (fun x => ?_)
  cases x with
  | some d =>
    have he : (fun u => primedEntryDistanceCode u j k) ⁻¹' {some d} =
        {u | ∀ᶠ n in atTop, primedEntryBoundaryStageDistance u n j k = d} := by
      ext u
      exact primedEntryEventualValue_eq_some_iff _ d
    rw [he]
    exact measurableSet_primedEntry_eventually j k d
  | none =>
    have he : (fun u => primedEntryDistanceCode u j k) ⁻¹' {none} =
        (⋃ d : WithBot ℕ,
          {u | ∀ᶠ n in atTop, primedEntryBoundaryStageDistance u n j k = d})ᶜ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
        Set.mem_iUnion, Set.mem_ofPred_eq]
      unfold primedEntryDistanceCode primedEntryEventualValue
      split_ifs <;> simp_all
    rw [he]
    exact (MeasurableSet.iUnion (measurableSet_primedEntry_eventually j k)).compl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The outer boundary index is -j.
For j = 0,1 the selector uses east and west of the retained C18 root; later
indices use west endpoints of LL.reverse at index j-2.
Proved downstream: see Recursive/PrimedEntryDecoderExists.lean (j ≤ 1) and
Recursive/HLRLdpFinal.lean (all indices). -/
@[expose] def PrimedEntryOuterVertexIdentification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hb : BoundaryHitWitnesses w) (j : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ a,
    primedEntryOuterVertex (kmswStage (primedCode (primedSimInput w) h) n) j = some a ∧
      primedLimitVertexMap w h a = boundaryVertex w hb (-(j : ℤ))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The endpoint obligation UR.reverse index k ↦ beta vertex k, proved below.
This isolates the ordered endpoint step from the already proved edge ordering. -/
@[expose] def PrimedEntryGlueVertexIdentification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (k : ℕ) : Prop :=
  primedLimitVertexMap w h
      (edgeEast (primedCode (primedSimInput w) h)
        (primedBeta0EdgeIndex w h hfin hb hfin k)) = kmswBeta0Vertices w hfin hb k

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The ordered glue endpoint obligation is proved by the C13 side flip, retaining
all geometric missing edges. Both its edge index and vertex index are k. -/
theorem primedEntryGlueVertexIdentification_proved (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (k : ℕ) :
    PrimedEntryGlueVertexIdentification w h hfin hb k := by
  let u := primedCode (primedSimInput w) h
  let B := primedIntervalBase (primedSimInput w) h k
  let I := primedBeta0EdgeIndex w h hfin hb hfin k
  have hc : u B = 1 := by
    cases k with
    | zero => exact primedCode_zero (primedSimInput w) h
    | succ k => exact (primedCrossing_codes w h k).1
  have hi : I = (kmswMissingRootStage u B).nextEdge + 1 :=
    primedBeta0EdgeIndex_eq_creation w h hfin hb hfin k
  have ha : I < (kmswMissingRootStage u (B + 1)).nextEdge := by
    rw [hi, kmswMissingRootStage, hc]
    change (kmswMissingRootStage u B).nextEdge + 1 <
      (kmswMissingRootStage u B).nextEdge + 2
    omega
  have hf : primedLimitSideFlip w h I = true := by
    rw [primedLimitSideFlip_eq_stage w h (B + 1) ⟨I, ha⟩]
    exact (primedSideFlip_eq_true_iff w h (B + 1) ⟨I, ha⟩).mpr
      ⟨k, Nat.lt_succ_self B, hi⟩
  have he := primedBeta0EdgeIndex_endpoint_sideflip w h hfin hb hfin k
  change (primedLimitSideFlip w h I = false ∧ _) ∨
    (primedLimitSideFlip w h I = true ∧ _) at he
  rcases he with he | he
  · rw [hf] at he
    cases he.1
  · change primedLimitVertexMap w h (edgeEast u I) = _
    rw [← he.2.1, primedBeta0EdgeIndex_maps_to_stream w h hfin hb hfin k]
    cases k with
    | zero => exact kmswBeta0Stream_start w hfin hb
    | succ k => exact kmswBeta0Stream_chain w hfin hb k

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The glue selector itself stabilizes to the east endpoint of the same indexed
beta edge preimage. This is a geometric vertex, not an ordinary root arrow. -/
theorem primedEntryGlueVertex_eventually (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (k : ℕ) :
    ∀ᶠ n in atTop,
      primedEntryGlueVertex (kmswStage (primedCode (primedSimInput w) h) n) k =
        some (edgeEast (primedCode (primedSimInput w) h)
          (primedBeta0EdgeIndex w h hfin hb hfin k)) := by
  let u := primedCode (primedSimInput w) h
  let B := primedIntervalBase (primedSimInput w) h k
  let I := primedBeta0EdgeIndex w h hfin hb hfin k
  filter_upwards [eventually_ge_atTop (max (B + 1) I)] with n hn
  have hB : B + 1 ≤ n := (Nat.le_max_left _ _).trans hn
  have hI : I ≤ n := (Nat.le_max_right _ _).trans hn
  have he : I < (kmswStage u n).nextEdge :=
    (kmsw_edge_allocated_by_self u I).trans_le (kmswStage_nextEdge_mono u hI)
  rw [primedEntryGlueVertex_same_index w h hfin hb k n hB]
  exact congrArg some (edge_endpoints_eq u he).2

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
H' transports every primed stage arrow with its edge ID and ordered endpoints. -/
@[expose] noncomputable def primedEntryStageToAmbient (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (n : ℕ) :
    Prefunctor (PrimedEntryVertex
      (kmswMissingRootStage (primedCode (primedSimInput w) h) n)) (PresentVertex w) where
  obj a := ⟨primedLimitVertexMap w h a.id⟩
  map {_ _} e := by
    let u := primedCode (primedSimInput w) h
    have hp : PrimedEdgePresent w h e.val := ⟨n, e.property.1, e.property.2.1⟩
    have hd := primedLimitEdge_data w h hp
    have he := (primedEntryStagePresent_iff u n e.val).mp
      ⟨e.property.1, e.property.2.1⟩
    have ha := kmswMissingRootStage_agree u n
    exact ⟨primedLimitEdgeMap w h e.val, hd.1,
      hd.2.2.1.trans (congrArg (primedLimitVertexMap w h)
        ((edge_endpoints_eq u he.2.1).1.symm.trans
          ((ha.2.2.1 e.val).symm.trans e.property.2.2.1))),
      hd.2.2.2.trans (congrArg (primedLimitVertexMap w h)
        ((edge_endpoints_eq u he.2.1).2.symm.trans
          ((ha.2.2.2.1 e.val).symm.trans e.property.2.2.2)))⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The H' image of a stage path preserves its natural length. -/
theorem primedEntryStageToAmbient_length (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (n : ℕ) {a b : PrimedEntryVertex
      (kmswMissingRootStage (primedCode (primedSimInput w) h) n)} (p : Path a b) :
    ((primedEntryStageToAmbient w h n).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Each transported path stays outside the hatted vertex set until its final vertex. -/
theorem primedEntryStageToAmbient_firstEntry (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (n : ℕ) {a b : PrimedEntryVertex
      (kmswMissingRootStage (primedCode (primedSimInput w) h) n)} (p : Path a b) :
    ∀ v ∈ ((primedEntryStageToAmbient w h n).mapPath p).vertices,
      v ≠ (primedEntryStageToAmbient w h n).obj b → v ∉ leftHatVertices w := by
  induction p with
  | nil =>
    intro v hv hne
    exact (hne (List.mem_singleton.mp hv)).elim
  | @cons b c p e ih =>
    let F := primedEntryStageToAmbient w h n
    let q := F.map e
    have hp : primePresentEdge w q.val :=
      (primedLimitEdgeMap_present_iff w h e.val).mp
        ⟨n, e.property.1, e.property.2.1⟩
    have hb : F.obj b ∉ leftHatVertices w := by
      intro hr
      have ht := leftHatVertices_closed hr (Hom.toPath q)
      apply hp.2
      constructor
      · change Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w q.val⟩
        rw [q.property.2.1]
        exact hr
      · change Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w q.val⟩
        rw [q.property.2.2]
        exact ht
    intro v hv hne
    rw [Prefunctor.mapPath_cons] at hv
    rcases (Path.mem_vertices_cons (F.mapPath p) q).mp hv with hv | hv
    · by_cases hvb : v = F.obj b
      · exact hvb ▸ hb
      · exact ih v hv hvb
    · exact (hne hv).elim

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
One direction of length identification is proved by H', with no extra premise. -/
theorem primedEntryStage_lengths_subset (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (n a b : ℕ) :
    pathLengths (⟨a⟩ : PrimedEntryVertex
      (kmswMissingRootStage (primedCode (primedSimInput w) h) n)) ⟨b⟩ ⊆
      leftPrimedEntryLengths w ⟨primedLimitVertexMap w h a⟩
        ⟨primedLimitVertexMap w h b⟩ := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(primedEntryStageToAmbient w h n).mapPath p,
    primedEntryStageToAmbient_length w h n p,
    primedEntryStageToAmbient_firstEntry w h n p⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The reverse path obligation: every ambient first-entry length lifts to a
primed stage. It is proved below; the forward inclusion is also proved above. -/
@[expose] def PrimedEntryPathLengthIdentification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (a b : ℕ) : Prop :=
  leftPrimedEntryLengths w ⟨primedLimitVertexMap w h a⟩ ⟨primedLimitVertexMap w h b⟩ ⊆
    ⋃ n : ℕ, pathLengths (⟨a⟩ : PrimedEntryVertex
      (kmswMissingRootStage (primedCode (primedSimInput w) h) n)) ⟨b⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every local vertex is allocated, so H' is injective on all natural vertex IDs. -/
private theorem primedEntryVertexMap_injective (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) : Function.Injective (primedLimitVertexMap w h) := by
  intro a b hab
  exact (primedLimit_maps_injective_on_allocated w h).2
    ((primedLocalIds_eventually_allocated w h).2 a)
    ((primedLocalIds_eventually_allocated w h).2 b) hab

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An ambient first-entry path lifts, preserving its length, to one finite primed stage.
The stage is constructed from the finitely many present edge preimages under H'. -/
private theorem primedEntryAmbientPath_lift (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    {x y : PresentVertex w} (p : Path x y) :
    ∀ a b : ℕ, x.id = primedLimitVertexMap w h a →
      y.id = primedLimitVertexMap w h b →
      (∀ v ∈ p.vertices, v ≠ y → v ∉ leftHatVertices w) →
      ∃ n, ∃ q : Path
        (⟨a⟩ : PrimedEntryVertex
          (kmswMissingRootStage (primedCode (primedSimInput w) h) n)) ⟨b⟩,
        q.length = p.length := by
  let u := primedCode (primedSimInput w) h
  have hinj := primedEntryVertexMap_injective w h
  induction p with
  | nil =>
    intro a b ha hb _
    have hab : a = b := hinj (ha.symm.trans hb)
    subst b
    exact ⟨0, Path.nil, rfl⟩
  | @cons y z p e ih =>
    intro a b ha hb hc
    have hz : z ∉ p.vertices := by
      have hnd := vertices_nodup_of_acyclic (presentVertex_acyclic w) (p.cons e)
      rw [Path.vertices_cons, List.nodup_concat] at hnd
      exact hnd.1
    have hyz : y ≠ z := fun hyz => hz (hyz ▸ p.end_mem_vertices)
    have hy : y ∉ leftHatVertices w :=
      hc y ((Path.mem_vertices_cons p e).mpr (Or.inl p.end_mem_vertices)) hyz
    have hnever : ∀ n, e.val ∉ stageReachablePresentEdges w n := by
      intro n hn
      obtain ⟨_, ht, _⟩ :=
        (stageReachablePresentEdges_iUnion_iff w e.val).mp ⟨n, hn⟩
      apply hy
      change Reachable (⟨0⟩ : PresentVertex w) y
      rw [e.property.2.1] at ht
      exact ht
    obtain ⟨f, hf, hfe⟩ := primedLimitEdgeComplement w h e.val e.property.1 hnever
    have hd := primedLimitEdge_data w h hf
    have hleft : y.id = primedLimitVertexMap w h (edgeWest u f) := by
      rw [← e.property.2.1, ← hfe]
      exact hd.2.2.1
    have hright : edgeEast u f = b := by
      apply hinj
      rw [← hd.2.2.2, hfe, e.property.2.2]
      exact hb
    have hc' : ∀ v ∈ p.vertices, v ≠ y → v ∉ leftHatVertices w := by
      intro v hv _
      exact hc v ((Path.mem_vertices_cons p e).mpr (Or.inl hv))
        (fun hvz => hz (hvz ▸ hv))
    obtain ⟨N, q, hq⟩ := ih a (edgeWest u f) ha hleft hc'
    obtain ⟨m, hm, hp⟩ := hf
    have he := (primedEntryStagePresent_iff u m f).mp ⟨hm, hp⟩
    let Q := max N m
    have hpQ := (primedEntryStagePresent_iff u Q f).mpr
      ⟨he.1, present_mono u he.2.1 he.2.2 Q (Nat.le_max_right N m)⟩
    have hbQ := (primedEntryStagePresent_iff u Q f).mp hpQ
    have hag := kmswMissingRootStage_agree u Q
    have hends := edge_endpoints_eq u hbQ.2.1
    let fQ : (⟨edgeWest u f⟩ : PrimedEntryVertex (kmswMissingRootStage u Q)) ⟶
        (⟨b⟩ : PrimedEntryVertex (kmswMissingRootStage u Q)) :=
      ⟨f, hpQ.1, hpQ.2,
        (hag.2.2.1 f).trans hends.1,
        (hag.2.2.2.1 f).trans (hends.2.trans hright)⟩
    refine ⟨Q, ((primedEntryStageToLater u N Q (Nat.le_max_left N m)).mapPath q).cons fQ,
      ?_⟩
    exact congrArg Nat.succ
      ((primedEntryStageToLater_length u N Q (Nat.le_max_left N m) q).trans hq)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The reverse path-length obligation is proved; every first-entry length appears
at a finite primed stage, including the empty path when the endpoints agree. -/
theorem primedEntryPathLengthIdentification_proved (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (a b : ℕ) : PrimedEntryPathLengthIdentification w h a b := by
  rintro k ⟨p, hp, hc⟩
  obtain ⟨n, q, hq⟩ := primedEntryAmbientPath_lift w h p a b rfl rfl hc
  exact Set.mem_iUnion.mpr ⟨n, q, hq.trans hp⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Exact equality of all attainable lengths under H', retaining unreachable pairs. -/
theorem primedEntryStage_lengths_union_eq (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a b : ℕ) :
    (⋃ n : ℕ, pathLengths (⟨a⟩ : PrimedEntryVertex
      (kmswMissingRootStage (primedCode (primedSimInput w) h) n)) ⟨b⟩) =
      leftPrimedEntryLengths w ⟨primedLimitVertexMap w h a⟩
        ⟨primedLimitVertexMap w h b⟩ := by
  apply Set.Subset.antisymm
  · intro k hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact primedEntryStage_lengths_subset w h n a b hn
  · exact primedEntryPathLengthIdentification_proved w h a b

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
For fixed local endpoints, the eventual stage distance equals the exact ambient
first-entry distance under H'. No boundary correspondence is assumed here. -/
theorem primedEntryStageDistance_identification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w) (a b : ℕ) :
    ∀ᶠ n in atTop,
      primedEntryStageDistance (primedCode (primedSimInput w) h) n a b =
        leftLengthSup (leftPrimedEntryLengths w ⟨primedLimitVertexMap w h a⟩
          ⟨primedLimitVertexMap w h b⟩) := by
  have he := primedEntryStageDistance_eventually (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin) a b
  rw [primedEntryStage_lengths_union_eq w h a b] at he
  exact he

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw input is
shift of compressed times. The explicit index maps are j ↦ -j and k ↦ k.
Glue stabilization, path exhaustion, and fixed-endpoint distance stabilization
are proved above. Proved downstream: see
Recursive/PrimedEntryDecoderExists.lean (j ≤ 1) and Recursive/HLRLdpFinal.lean
(all indices). -/
@[expose] def PrimedEntryDistanceCodeIdentification : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure,
    let w := fun i => ω (i + 1)
    ∀ (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (j k : ℕ),
      primedEntryDistanceCode (hatLawPrimedCodes ω) j k =
        some (leftLengthSup (leftPrimedEntryLengths w
          ⟨busemannBoundaryIdTotal ω (-(j : ℤ))⟩ ⟨kmswBeta0Vertices w hfin hb k⟩))

end DirectedDistances.Recursive
