module

public import DirectedDistances.Recursive.PrimedEntryDistanceCode
public import DirectedDistances.Recursive.BusemannLeftSideDecompositionSdp

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver MeasureTheory Filter

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The shortest path length using primed-present arrows at a finite missing-root stage.
An unreachable pair has value `⊤`, and the retained root is not a directed arrow. -/
@[expose] noncomputable def primedEntryStageSdp (u : ℕ → Fin 3) (n a b : ℕ) : ℕ∞ :=
  leftLengthMin (pathLengths (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The SDP code is the minimum over the union of the primed stage path-length sets. -/
@[expose] noncomputable def primedEntrySdpCode (u : ℕ → Fin 3) (a b : ℕ) : ℕ∞ :=
  leftLengthMin (⋃ n : ℕ, pathLengths
    (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Increasing stage path sets make their minimum equal the union minimum at every
sufficiently large stage. If the union is empty, every stage remains unreachable. -/
theorem primedEntryStageSdp_eventually (u : ℕ → Fin 3) (a b : ℕ) :
    ∀ᶠ n in atTop, primedEntryStageSdp u n a b = primedEntrySdpCode u a b := by
  let T (n : ℕ) : Set ℕ := pathLengths
    (⟨a⟩ : PrimedEntryVertex (kmswMissingRootStage u n)) ⟨b⟩
  let S : Set ℕ := ⋃ n : ℕ, T n
  change ∀ᶠ n in atTop, leftLengthMin (T n) = leftLengthMin S
  by_cases hS : S.Nonempty
  · obtain ⟨N, hN⟩ := Set.mem_iUnion.mp (Nat.sInf_mem hS)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hleast : IsLeast (T n) (sInf S) := by
      constructor
      · exact primedEntryStage_lengths_mono u a b hn hN
      · intro m hm
        exact Nat.sInf_le (Set.mem_iUnion.mpr ⟨n, hm⟩)
    have hT : (T n).Nonempty := ⟨sInf S, hleast.1⟩
    have hnat : sInf (T n) = sInf S := by
      apply Nat.le_antisymm
      · exact Nat.sInf_le hleast.1
      · exact hleast.2 (Nat.sInf_mem hT)
    have hleft : leftLengthMin (T n) = ((sInf S : ℕ) : ℕ∞) := by
      rw [leftLengthMin, dite_eq_left hT, hnat]
    have hright : leftLengthMin S = ((sInf S : ℕ) : ℕ∞) := by
      rw [leftLengthMin, dite_eq_left hS]
    exact hleft.trans hright.symm
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    filter_upwards [] with n
    have hTempty : T n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro m hm
      have hmS : m ∈ S := Set.mem_iUnion.mpr ⟨n, hm⟩
      rw [hSempty] at hmS
      exact hmS
    rw [hTempty, hSempty]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The union-minimum code equals `d` exactly when the finite-stage minima are
eventually `d`, including `⊤` for unreachable endpoint pairs. -/
theorem primedEntrySdpCode_eq_eventually (u : ℕ → Fin 3) (a b : ℕ) (d : ℕ∞) :
    primedEntrySdpCode u a b = d ↔
      ∀ᶠ n in atTop, primedEntryStageSdp u n a b = d := by
  constructor
  · intro h
    exact (primedEntryStageSdp_eventually u a b).mono (fun _ hn => hn.trans h)
  · intro h
    obtain ⟨n, hn⟩ := (primedEntryStageSdp_eventually u a b).and h |>.exists
    exact hn.1.symm.trans hn.2

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The missing-root state depends only on the indicated finite input prefix. -/
private theorem primedEntryMissingRootStage_congr {u v : ℕ → Fin 3} {n : ℕ}
    (h : ∀ i < n, u i = v i) :
    kmswMissingRootStage u n = kmswMissingRootStage v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change kmswStep (kmswMissingRootStage u n) (u n) =
      kmswStep (kmswMissingRootStage v n) (v n)
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Each finite-stage shortest distance depends only on the corresponding finite input
prefix. -/
theorem measurable_primedEntryStageSdp (n a b : ℕ) :
    @Measurable (ℕ → Fin 3) ℕ∞ _ ⊤ (fun u => primedEntryStageSdp u n a b) := by
  let : MeasurableSpace ℕ∞ := ⊤
  refine measurable_of_factors_prefix n _ (fun u v h => ?_)
  unfold primedEntryStageSdp
  rw [primedEntryMissingRootStage_congr h]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An eventual equality of finite-stage distances is a countable union of
countable intersections of measurable finite-prefix events. -/
private theorem measurableSet_primedEntrySdp_eventually (a b : ℕ) (d : ℕ∞) :
    MeasurableSet {u | ∀ᶠ n in atTop, primedEntryStageSdp u n a b = d} := by
  let : MeasurableSpace ℕ∞ := ⊤
  have he : {u | ∀ᶠ n in atTop, primedEntryStageSdp u n a b = d} =
      ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n),
        {u | primedEntryStageSdp u n a b = d} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_atTop]
  rw [he]
  exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n =>
    MeasurableSet.iInter (fun _ => measurableSet_eq_fun
      (measurable_primedEntryStageSdp n a b) measurable_const)))

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The stable shortest-distance code is measurable in the input sequence. -/
theorem measurable_primedEntrySdpCode (a b : ℕ) :
    @Measurable (ℕ → Fin 3) ℕ∞ _ ⊤ (fun u => primedEntrySdpCode u a b) := by
  let : MeasurableSpace ℕ∞ := ⊤
  refine measurable_to_countable' (fun d => ?_)
  have he : (fun u => primedEntrySdpCode u a b) ⁻¹' {d} =
      {u | ∀ᶠ n in atTop, primedEntryStageSdp u n a b = d} := by
    ext u
    exact (primedEntrySdpCode_eq_eventually u a b d)
  rw [he]
  exact measurableSet_primedEntrySdp_eventually a b d

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
H' identifies the code with the minimum ambient first-entry path length; the
template's proved path-length identification supplies the exact path-set equality. -/
theorem primedEntrySdpCode_identification (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a b : ℕ) :
    primedEntrySdpCode (primedCode (primedSimInput w) h) a b =
      leftLengthMin (leftPrimedEntryLengths w ⟨primedLimitVertexMap w h a⟩
        ⟨primedLimitVertexMap w h b⟩) := by
  unfold primedEntrySdpCode
  rw [primedEntryStage_lengths_union_eq w h a b]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Boundary-coordinate identification is conditional on the template's open outer
vertex Prop. The glue endpoint uses the proved C13 ordering, retaining the C18 root. -/
theorem primedEntrySdpCode_boundary_identification (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (j k : ℕ)
    (houter : PrimedEntryOuterVertexIdentification w h hb j) :
    ∃ a, primedLimitVertexMap w h a = boundaryVertex w hb (-(j : ℤ)) ∧
      primedEntrySdpCode (primedCode (primedSimInput w) h) a
          (edgeEast (primedCode (primedSimInput w) h)
            (primedBeta0EdgeIndex w h hfin hb hfin k)) =
        leftLengthMin (leftPrimedEntryLengths w
          ⟨boundaryVertex w hb (-(j : ℤ))⟩ ⟨kmswBeta0Vertices w hfin hb k⟩) := by
  obtain ⟨_, hstage⟩ := houter.exists
  obtain ⟨a, _, ha⟩ := hstage
  have hglue := primedEntryGlueVertexIdentification_proved w h hfin hb k
  have hid := primedEntrySdpCode_identification w h a
    (edgeEast (primedCode (primedSimInput w) h)
      (primedBeta0EdgeIndex w h hfin hb hfin k))
  rw [ha, hglue] at hid
  exact ⟨a, ha, hid⟩

end DirectedDistances.Recursive
