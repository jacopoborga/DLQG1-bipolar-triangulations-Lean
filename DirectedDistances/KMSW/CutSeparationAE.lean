module

public import DirectedDistances.KMSW.CutSeparation
public import DirectedDistances.KMSW.CutEquivalenceAE
public import DirectedDistances.KMSW.LocalFinitenessUpperChain
public import DirectedDistances.RandomWalk.BlockBoundUnconditional
public import DirectedDistances.RandomWalk.PitmanCodes

/-! # Almost-sure cut separation and infinite directed paths

Helpers combining the success event `eqn-walk-bdy-event` -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open DirectedDistances.RandomWalk

private theorem measurable_vectorPitman_cutSeparation : Measurable vectorPitman := by
  have hf : Measurable (fun z : ℕ → ℤ × ℤ => fun k => (z k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hf).prodMk
    (((measurable_pi_apply n).snd).add ((measurable_globalLazyRunningMinimum n).comp hf))

/-- Almost surely the record inequalities hold at infinitely many bookkeeping times for the
Pitman-flipped iid codes. The success event at walk index `n + 1` gives bookkeeping time -/
theorem pitmanCodes_ae_infinite_cutSeparation_records :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite := by
  have hmeas : Measurable (fun ω : ℕ → Fin 3 =>
      fun k => vectorPitman (codeWalk ω) k) :=
    measurable_vectorPitman_cutSeparation.comp measurable_codeWalk
  have hS := ae_of_ae_map hmeas.aemeasurable
    (by rw [map_vectorPitman_codeWalk]
        exact conditionedVectorPathLaw_ae_infinite_success)
  filter_upwards [hS] with ω hS
  let w : ℕ → Fin 3 := pitmanCode (fun i => ω (i + 1))
  have hPw : ∀ n, vectorPitman (codeWalk ω) n = integrateCodes w n := by
    intro n
    rw [integrateCodes_pitmanCode]
    rfl
  let S : Set ℕ := {n : ℕ | (∀ k, k < n + 1 →
      (vectorPitman (codeWalk ω) (n + 1)).2 ≤
        (vectorPitman (codeWalk ω) k).2 - 1) ∧
      ∀ i, n + 1 ≤ i →
        (vectorPitman (codeWalk ω) (n + 1)).1 ≤
          (vectorPitman (codeWalk ω) i).1}
  have hSinf : S.Infinite := hS
  have hinj : Set.InjOn Nat.succ S := by
    intro a ha b hb hab
    exact Nat.succ.inj hab
  have himage : (Nat.succ '' S).Infinite := hSinf.image hinj
  have hsub : Nat.succ '' S ⊆
      {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j} := by
    rintro n ⟨k, hk, rfl⟩
    constructor
    · intro j hj
      rw [RandomWalk.kmsw_R_eq, RandomWalk.kmsw_R_eq, ← hPw, ← hPw]
      exact hk.1 j hj
    · intro j hj
      rw [RandomWalk.kmsw_L_eq, RandomWalk.kmsw_L_eq, ← hPw, ← hPw]
      exact hk.2 j hj
  change {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
    ∀ j, n ≤ j → L w n ≤ L w j}.Infinite
  exact himage.mono hsub

private theorem record_active_east_successor (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1) :
    (kmswStage w n).east (act w n) + 1 = (kmswStage w n).nextVertex := by
  by_cases hn : n = 0
  · subst n
    simp [kmswStage, kmswInit, act]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let k := n - 1
    have hnk : n = k + 1 := by dsimp [k]; omega
    have hRstep : R w (k + 1) = R w k +
        (RandomWalk.lazyTwoDimensionalStep (w k)).2 :=
      Finset.sum_range_succ _ _
    have hdown : w k = 2 := by
      have hstrict := hA k (by omega)
      rw [hnk] at hstrict
      rw [hRstep] at hstrict
      by_cases h2 : (w k).val = 2
      · exact Fin.ext h2
      · have hval : (w k).val = 0 ∨ (w k).val = 1 := by
          have hlt := (w k).isLt
          omega
        rcases hval with h0 | h1
        · have hc : w k = 0 := Fin.ext h0
          rw [hc, RandomWalk.lazyTwoDimensionalStep_zero] at hstrict
          omega
        · have hc : w k = 1 := Fin.ext h1
          rw [hc, RandomWalk.lazyTwoDimensionalStep_one] at hstrict
          omega
    have hRdown : R w (k + 1) = R w k - 1 := by
      rw [hRstep, hdown, RandomWalk.lazyTwoDimensionalStep_two]
      ring
    have hmin : minR w k = R w k := by
      obtain ⟨i, hik, hmin⟩ := runningMin_attained (R w) k
      change minR w k = R w i at hmin
      have hlow : R w k ≤ R w i := by
        have hi := hA i (by omega)
        rw [hnk, hRdown] at hi
        omega
      have hle := runningMin_le (R w) k k (le_refl k)
      change minR w k ≤ R w k at hle
      omega
    have hlen := kmswStage_UR_length w k
    have hURlen : ((kmswStage w k).UR.length : ℤ) = 0 := by
      rw [hlen, hmin]
      ring
    have hUR : (kmswStage w k).UR.length = 0 := by omega
    have hURnil : (kmswStage w k).UR = [] := List.length_eq_zero_iff.mp hUR
    have hStage : kmswStage w n =
        kmswStepOfStep (kmswStage w k) .down := by
      rw [hnk]
      simp [kmswStage, kmswStep, kmswCodeStep, hdown]
    have hact : act w n = (kmswStage w k).nextEdge := by
      change (kmswStage w n).active = (kmswStage w k).nextEdge
      rw [hStage]
      simp [kmswStepOfStep, hURnil, State.addEdge]
    rw [hStage, hact]
    simp [kmswStepOfStep, hURnil, State.addEdge]

/-- In a locally finite KMSW map, a sequence of pairwise distinct edges cannot have all
endpoints bounded. -/
theorem kmsw_distinct_edge_sequence_vertices_unbounded (w : ℕ → Fin 3)
    (hInc : ∀ v : ℕ, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (e : ℕ → ℕ) (hinj : Function.Injective e) :
    ∀ B : ℕ, ∃ i, B ≤ edgeWest w (e i) ∨ B ≤ edgeEast w (e i) := by
  intro B
  by_contra hbound
  push Not at hbound
  let I (v : ℕ) : Set ℕ := {f : ℕ | ∃ n, f < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west f = v ∨ (kmswStage w n).east f = v)}
  let U : Set ℕ := ⋃ v ∈ (Finset.range B : Set ℕ), I v
  have hUfin : U.Finite := by
    exact (Finset.range B).finite_toSet.biUnion (fun v _ => hInc v)
  have hrange : Set.range e ⊆ U := by
    rintro f ⟨i, rfl⟩
    have halloc := CutConverse.allocation_count w (e i)
    have hself : e i < (kmswStage w (e i)).nextEdge := by omega
    have hW : edgeWest w (e i) = (kmswStage w (e i)).west (e i) := rfl
    have hWlt : edgeWest w (e i) < B := by
      exact (hbound i).1
    change e i ∈ ⋃ v ∈ (Finset.range B : Set ℕ), I v
    refine Set.mem_iUnion.mpr ⟨edgeWest w (e i), ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hWlt, ?_⟩
    refine ⟨e i, hself, Or.inl ?_⟩
    rw [hW]
  have hfiniteRange : (Set.range e).Finite := hUfin.subset hrange
  have hinfinite : (Set.range e).Infinite := Set.infinite_range_of_injective hinj
  exact False.elim (hinfinite.not_finite hfiniteRange)

/-- Every infinite directed edge sequence from the source with pairwise distinct edges visits
the west endpoint of each record active edge, provided the KMSW map is locally finite. -/
theorem kmswInfinitePath_meets_recordVertex (w : ℕ → Fin 3) (n : ℕ)
    (hA : ∀ j < n, R w n ≤ R w j - 1)
    (hB : ∀ j, n ≤ j → L w n ≤ L w j)
    (e : ℕ → ℕ)
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (hstart : edgeWest w (e 0) = 0)
    (hinj : Function.Injective e)
    (hInc : ∀ v : ℕ, {f : ℕ | ∃ m, f < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west f = v ∨ (kmswStage w m).east f = v)}.Finite) :
    ∃ i, edgeWest w (e i) = (kmswStage w n).west (act w n) ∨
      edgeEast w (e i) = (kmswStage w n).west (act w n) := by
  have haSucc := record_active_east_successor w n hA
  have hroot : 2 ≤ (kmswStage w n).nextVertex := by
    have hmono := CutConverse.nextVertex_mono w (Nat.zero_le n)
    simpa [kmswStage, kmswInit] using hmono
  have hapos : 0 < (kmswStage w n).east (act w n) := by omega
  let v := (kmswStage w n).west (act w n)
  let a := (kmswStage w n).east (act w n)
  let Before := {u | u < (kmswStage w n).nextVertex ∧ u ≠ v ∧ u ≠ a}
  have hstart' : edgeWest w (e 0) ∈ Before ∨ edgeWest w (e 0) = v := by
    by_cases hv : v = 0
    · right
      change edgeWest w (e 0) = (kmswStage w n).west (act w n)
      rw [hstart]
      exact hv.symm
    · left
      rw [hstart]
      change 0 < (kmswStage w n).nextVertex ∧
        0 ≠ (kmswStage w n).west (act w n) ∧
        0 ≠ (kmswStage w n).east (act w n)
      exact ⟨by omega, Ne.symm hv, by omega⟩
  obtain ⟨i, hlarge⟩ :=
    kmsw_distinct_edge_sequence_vertices_unbounded w hInc e hinj a
  let es : List ℕ := (List.range (i + 1)).map e
  have hne : es ≠ [] := by simp [es]
  have hchain : List.IsChain (fun f g => edgeEast w f = edgeWest w g) es := by
    change List.IsChain (fun f g => edgeEast w f = edgeWest w g)
      ((List.range (i + 1)).map e)
    rw [List.isChain_map, List.isChain_range_succ]
    intro j hj
    exact hpath j
  have hhead : edgeWest w (es.head hne) ∈
      {u | u < (kmswStage w n).nextVertex ∧
        u ≠ (kmswStage w n).west (act w n) ∧
        u ≠ (kmswStage w n).east (act w n)} ∨
      edgeWest w (es.head hne) = (kmswStage w n).west (act w n) := by
    simpa [es, hstart, v, Before] using hstart'
  have hafter : ∃ f ∈ es,
      (kmswStage w n).east (act w n) ≤ edgeWest w f ∨
      (kmswStage w n).east (act w n) ≤ edgeEast w f := by
    refine ⟨e i, ?_, ?_⟩
    · change e i ∈ (List.range (i + 1)).map e
      apply List.mem_map.mpr
      exact ⟨i, List.mem_range.mpr (by omega), rfl⟩
    · simpa [a] using hlarge
  obtain ⟨f, hfmem, hincident⟩ :=
    kmswFinitePath_meets_recordVertex w n hA hB es hne hchain hhead hafter
  obtain ⟨j, hjrange, hjeq⟩ := List.mem_map.mp hfmem
  refine ⟨j, ?_⟩
  have hjendpoint := hincident
  rw [← hjeq] at hjendpoint
  exact hjendpoint

/-- Almost surely there are infinitely many distinct KMSW vertices that every infinite
directed edge path from the source with pairwise distinct edges visits. -/
theorem pitmanCodes_ae_infinite_unavoidable_recordVertices :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      {v : ℕ | ∀ e : ℕ → ℕ,
        (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) →
        edgeWest w (e 0) = 0 → Function.Injective e →
        ∃ i, edgeWest w (e i) = v ∨ edgeEast w (e i) = v}.Infinite := by
  have hrecords := pitmanCodes_ae_infinite_cutSeparation_records
  have hequiv := pitmanCodes_ae_cut_equiv
  have hinc := pitmanCodes_ae_finite_incident_edges
  filter_upwards [hrecords, hequiv, hinc] with ω hrecords hequiv hinc
  let w : ℕ → Fin 3 := pitmanCode (fun i => ω (i + 1))
  let G : Set ℕ := {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
    ∀ j, n ≤ j → L w n ≤ L w j}
  have hG : G.Infinite := hrecords
  have hfirst : ∀ n ∈ G, ∀ j < n, activeInitial w j ≠ activeInitial w n := by
    intro n hn j hj
    have hiff := hequiv n
    have hrecordsN : (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j := hn
    exact ((hiff.mpr hrecordsN).2 j hj)
  have hinj : Set.InjOn (activeInitial w) G := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact False.elim ((hfirst b hb a hlt) hab)
    · exact heq
    · exact False.elim ((hfirst a ha b hgt) hab.symm)
  have himage : (activeInitial w '' G).Infinite := hG.image hinj
  have hsub : activeInitial w '' G ⊆
      {v : ℕ | ∀ e : ℕ → ℕ,
        (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) →
        edgeWest w (e 0) = 0 → Function.Injective e →
        ∃ i, edgeWest w (e i) = v ∨ edgeEast w (e i) = v} := by
    rintro v ⟨n, hn, rfl⟩ e hpath hstart' heinj
    have hnrec : (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j := hn
    have hincident := kmswInfinitePath_meets_recordVertex w n hnrec.1 hnrec.2
      e hpath hstart' heinj hinc
    rw [← CutConverse.activeInitial_eq] at hincident
    exact hincident
  change {v : ℕ | ∀ e : ℕ → ℕ,
    (∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) →
    edgeWest w (e 0) = 0 → Function.Injective e →
    ∃ i, edgeWest w (e i) = v ∨ edgeEast w (e i) = v}.Infinite
  exact himage.mono hsub

end DirectedDistances.KMSW

