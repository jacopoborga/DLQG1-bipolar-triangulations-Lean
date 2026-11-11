/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StoppedWalkLaw

/-! # Countable stopped-walk decomposition

This file develops the countable walk-cylinder decomposition and normalization
in the walk-level half of Lemma 3.11 (`lem-kmsw-boltzmann`,
the Theorem 3.5 bijection, including the isomorphism-class carrier with `m₀`,
and is not claimed here. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Dependent index of a stopped walk cylinder: its stopping time, left length,
and admissible finite word. -/
@[expose] def StoppedWalkIndex (r : ℕ) :=
  Σ n : ℕ, Σ ell : ℕ, KMSWWalkClass ell r n

instance instCountableStoppedWalkIndex (r : ℕ) : Countable (StoppedWalkIndex r) := by
  unfold StoppedWalkIndex
  infer_instance

/-- The set carried by an index of `StoppedWalkIndex`. The zero-time layer is -/
@[expose] def stoppedWalkIndexSet {r : ℕ} (i : StoppedWalkIndex r) :
    Set (ℕ → Fin 3) :=
  if 1 ≤ i.1 then stoppedCylinder i.2.2 else ∅

instance instMeasurableSpaceStoppedWalkIndexOption (r : ℕ) :
    MeasurableSpace (Option (StoppedWalkIndex r)) := ⊤

/-- The stopped finite-walk index on the conditioning event, and `none` off it.
This helper is for the walk-level law in Lemma 3.11; the map-level paper law
still requires the Theorem 3.5 bijection. -/
@[expose] noncomputable def stoppedIndex (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) : Option (StoppedWalkIndex r) := by
  classical
  exact if hE : ω ∈ boltzmannEvent r then
    let ell := (L (boltzmannKMSWStream ω) (boltzmannTau r ω)).toNat
    let c : KMSWWalkClass ell r (boltzmannTau r ω) :=
      ⟨stoppedWord r ω, (stoppedWord_admissible r hr ω hE).1⟩
    some ⟨boltzmannTau r ω, ⟨ell, c⟩⟩
  else none

private theorem finiteWord_integrate_eq_of_prefix {ell ell' r n : ℕ}
    (c : KMSWWalkClass ell r n) (c' : KMSWWalkClass ell' r n)
    (ω : ℕ → Fin 3)
    (hprefix : ∀ i : Fin (n - 1), ω (i.val + 1) = c.val i)
    (hprefix' : ∀ i : Fin (n - 1), ω (i.val + 1) = c'.val i)
    (k : ℕ) (hk : k ≤ n - 1) :
    integrateCodes (finiteCodeExtend c.val) k =
      integrateCodes (finiteCodeExtend c'.val) k := by
  unfold integrateCodes
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hit : i < n - 1 := lt_of_lt_of_le hik hk
  have hcode : c.val ⟨i, hit⟩ = c'.val ⟨i, hit⟩ := by
    exact (hprefix ⟨i, hit⟩).symm.trans (hprefix' ⟨i, hit⟩)
  simp [finiteCodeExtend, hit, hcode]

/-- If two indexed stopped cylinders intersect, the first-hit time, endpoint
length, and word all agree; hence the dependent indices agree. -/
theorem stoppedWalkIndex_eq_of_inter {r : ℕ}
    (i j : StoppedWalkIndex r) (ω : ℕ → Fin 3)
    (hi : ω ∈ stoppedWalkIndexSet i) (hj : ω ∈ stoppedWalkIndexSet j) :
    i = j := by
  classical
  rcases i with ⟨n, ⟨ell, c⟩⟩
  rcases j with ⟨n', ⟨ell', c'⟩⟩
  by_cases hn : 1 ≤ n
  · by_cases hn' : 1 ≤ n'
    · simp [stoppedWalkIndexSet, hn, hn'] at hi hj
      rcases hi with ⟨hprefix, hlast⟩
      rcases hj with ⟨hprefix', hlast'⟩
      have hslice := stoppedCylinder_subset_eventSlice hn c ⟨hprefix, hlast⟩
      have hslice' := stoppedCylinder_subset_eventSlice hn' c' ⟨hprefix', hlast'⟩
      have hnn' : n = n' := hslice.2.symm.trans hslice'.2
      subst n'
      have hint := finiteWord_integrate_eq_of_prefix c c' ω hprefix hprefix'
        (n - 1) le_rfl
      have hend := c.property.1
      have hend' := c'.property.1
      rw [hint] at hend
      have hell : ell = ell' := by
        have hfst := congrArg Prod.fst (hend.symm.trans hend')
        dsimp at hfst
        omega
      subst ell'
      have hc : c = c' := by
        apply Subtype.ext
        funext k
        exact (hprefix k).symm.trans (hprefix' k)
      subst c'
      rfl
    · simp [stoppedWalkIndexSet, hn'] at hj
  · simp [stoppedWalkIndexSet, hn] at hi

/-- The stopped-cylinder family indexed by `(n, ℓ, c)` is pairwise disjoint.
Source: the first-hit decomposition in Lemma 3.11, -/
theorem stoppedWalkIndexSet_pairwiseDisjoint {r : ℕ} (_hr : 1 ≤ r) :
    Pairwise (fun i j : StoppedWalkIndex r =>
      Disjoint (stoppedWalkIndexSet i) (stoppedWalkIndexSet j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact hij (stoppedWalkIndex_eq_of_inter i j ω hi hj)

private theorem measurable_stoppedWalkIndexSet {r : ℕ}
    (i : StoppedWalkIndex r) : MeasurableSet (stoppedWalkIndexSet i) := by
  classical
  by_cases hn : 1 ≤ i.1
  · simp only [stoppedWalkIndexSet, hn, ↓reduceIte]
    have hpref : Measurable (fun ω : ℕ → Fin 3 =>
        fun j : Fin (i.1 - 1) => ω (j.val + 1)) :=
      Measurable.of_eval fun j => measurable_pi_apply (j.val + 1)
    have hlast : Measurable (fun ω : ℕ → Fin 3 => ω i.1) :=
      measurable_pi_apply i.1
    rw [show stoppedCylinder i.2.2 =
        {ω : ℕ → Fin 3 | (fun j : Fin (i.1 - 1) => ω (j.val + 1)) = i.2.2.val} ∩
          {ω : ℕ → Fin 3 | ω i.1 = 2} by
      ext ω
      simp [stoppedCylinder, funext_iff]]
    exact (hpref (measurableSet_singleton i.2.2.val)).inter
      (hlast (measurableSet_singleton 2))
  · simp only [stoppedWalkIndexSet, hn, ↓reduceIte]
    exact MeasurableSet.empty

/-- The conditioning event is exactly the union of the positive-time stopped
walk cylinders. The event already includes existence of a finite hit, so this
is an exact equality rather than an almost-sure modification. Source: Lemma -/
theorem boltzmannEvent_eq_iUnion_stoppedWalkIndex (r : ℕ) (hr : 1 ≤ r) :
    boltzmannEvent r = ⋃ i : StoppedWalkIndex r, stoppedWalkIndexSet i := by
  classical
  ext ω
  constructor
  · intro hE
    have hhit : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := by
      rcases hE with ⟨n, hn, _⟩
      exact ⟨n, hn⟩
    have hτhit := boltzmann_tau_spec r ω hhit
    have hτpos : 1 ≤ boltzmannTau r ω := by
      by_contra h
      have : boltzmannTau r ω = 0 := by omega
      rw [this, codeWalk_zero] at hτhit
      omega
    have hslice := stoppedEventSlice_eq_walkCylinders r (boltzmannTau r ω)
      hr hτpos
    have hτ : ω ∈ {ω | ω ∈ boltzmannEvent r ∧
        boltzmannTau r ω = boltzmannTau r ω} := ⟨hE, rfl⟩
    have hdecomp := (Set.ext_iff.mp hslice) ω |>.mp hτ
    rcases Set.mem_iUnion.mp hdecomp with ⟨ell, hdecomp⟩
    rcases Set.mem_iUnion.mp hdecomp with ⟨c, hc⟩
    refine Set.mem_iUnion.mpr ⟨⟨boltzmannTau r ω, ⟨ell, c⟩⟩, ?_⟩
    simp [stoppedWalkIndexSet, hτpos, hc]
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
    by_cases hn : 1 ≤ i.1
    · simp [stoppedWalkIndexSet, hn] at hi
      exact (stoppedCylinder_subset_eventSlice hn i.2.2 hi).1
    · simp [stoppedWalkIndexSet, hn] at hi

/-- On the conditioning event, `stoppedIndex` returns an index whose cylinder
contains the original code stream. -/
private theorem stoppedIndex_spec (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) :
    ∃ i : StoppedWalkIndex r,
      stoppedIndex r hr ω = some i ∧ ω ∈ stoppedWalkIndexSet i := by
  classical
  have hhit : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := by
    rcases hE with ⟨n, hn, _⟩
    exact ⟨n, hn⟩
  have hτpos : 1 ≤ boltzmannTau r ω := by
    have hτhit := boltzmann_tau_spec r ω hhit
    by_contra h
    have hτzero : boltzmannTau r ω = 0 := by omega
    rw [hτzero, codeWalk_zero] at hτhit
    omega
  let n := boltzmannTau r ω
  let ell := (L (boltzmannKMSWStream ω) n).toNat
  have hadm := stoppedWord_admissible r hr ω hE
  let c : KMSWWalkClass ell r n := ⟨stoppedWord r ω, by
    dsimp [ell, n]
    exact hadm.1⟩
  let i : StoppedWalkIndex r := ⟨n, ⟨ell, c⟩⟩
  have hobs := boltzmann_boundary_observable r hr ω hE
  dsimp only at hobs
  rcases hobs with ⟨_, hlast, _, _, _, _, _, _⟩
  have hcyl : ω ∈ stoppedCylinder c := by
    constructor
    · intro j
      rfl
    · simpa [n] using hlast
  have hi : ω ∈ stoppedWalkIndexSet i := by
    simp [stoppedWalkIndexSet, i, n, hτpos, hcyl]
  have hidx : stoppedIndex r hr ω = some i := by
    simp [stoppedIndex, hE, i, n, ell, c]
  exact ⟨i, hidx, hi⟩

/-- The fiber of `stoppedIndex` over a positive-time walk class is exactly its
stopped cylinder. This gives the required countable-codomain measurability and
singleton-law calculation for the walk-level pushforward. -/
theorem stoppedIndex_preimage_singleton (r : ℕ) (hr : 1 ≤ r)
    (i : StoppedWalkIndex r) :
    stoppedIndex r hr ⁻¹' {some i} = stoppedWalkIndexSet i := by
  classical
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro heq
    by_cases hE : ω ∈ boltzmannEvent r
    · obtain ⟨j, hj, hcyl⟩ := stoppedIndex_spec r hr ω hE
      have hji : j = i := Option.some.inj (hj.symm.trans heq)
      rw [← hji]
      exact hcyl
    · simp [stoppedIndex, hE] at heq
  · intro hi
    by_cases hn : 1 ≤ i.1
    · have hicyl : ω ∈ stoppedCylinder i.2.2 := by
        simpa [stoppedWalkIndexSet, hn] using hi
      have hslice := stoppedCylinder_subset_eventSlice hn i.2.2 hicyl
      obtain ⟨j, hj, hcyl⟩ := stoppedIndex_spec r hr ω hslice.1
      have hji := stoppedWalkIndex_eq_of_inter j i ω hcyl hi
      subst j
      exact hj
    · simp [stoppedWalkIndexSet, hn] at hi

/-- The stopped-index map is measurable. Its codomain is countable and is
given the discrete measurable space. -/
theorem measurable_stoppedIndex (r : ℕ) (hr : 1 ≤ r) :
    Measurable (stoppedIndex r hr) := by
  apply measurable_to_countable
  intro ω
  by_cases hE : ω ∈ boltzmannEvent r
  · obtain ⟨i, hi, _⟩ := stoppedIndex_spec r hr ω hE
    rw [show {stoppedIndex r hr ω} = {some i} by rw [hi],
      stoppedIndex_preimage_singleton]
    exact measurable_stoppedWalkIndexSet i
  · have hnone : stoppedIndex r hr ω = none := by
      simp [stoppedIndex, hE]
    rw [show {stoppedIndex r hr ω} = {none} by rw [hnone]]
    have hEmeas : MeasurableSet (boltzmannEvent r) := by
      rw [boltzmannEvent_eq_iUnion_stoppedWalkIndex r hr]
      exact MeasurableSet.iUnion measurable_stoppedWalkIndexSet
    have hnonePre : stoppedIndex r hr ⁻¹' {none} = (boltzmannEvent r)ᶜ := by
      ext x
      simp [stoppedIndex]
    rw [hnonePre]
    exact hEmeas.compl

/-- Normalization of the walk-level stopped-word weights in Lemma 3.11.
The summand is restricted to positive stopping times; at each such time there
map-level statement still needs the Theorem 3.5 bijection. -/
theorem iidCodeMeasure_boltzmannEvent_eq_tsum_walkWeights
    (r : ℕ) (hr : 1 ≤ r) :
    iidCodeMeasure (boltzmannEvent r) =
      ∑' n : ℕ, ∑' ell : ℕ,
        if 1 ≤ n then
          (Fintype.card (KMSWWalkClass ell r n) : ENNReal) *
            (1 / 3 : ENNReal) ^ n
        else 0 := by
  classical
  rw [boltzmannEvent_eq_iUnion_stoppedWalkIndex r hr]
  rw [measure_iUnion (stoppedWalkIndexSet_pairwiseDisjoint hr)
    measurable_stoppedWalkIndexSet]
  change (∑' i : (Σ n : ℕ, Σ ell : ℕ, KMSWWalkClass ell r n),
      iidCodeMeasure (stoppedWalkIndexSet i)) = _
  rw [tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_sigma']
  apply tsum_congr
  intro ell
  by_cases hn : 1 ≤ n
  · simp only [stoppedWalkIndexSet, hn, ↓reduceIte]
    rw [tsum_fintype]
    simp_rw [iidCodeMeasure_stoppedCylinder_mass hn]
    simp
  · simp [hn, stoppedWalkIndexSet]

/-- The pushforward of the conditioned code law assigns mass `3^(-n)/P(E)`
to every positive-time stopped walk class. This is the walk-index law in the
walk-level half of Lemma 3.11; the paper's map-level law still needs Theorem -/
theorem boltzmann_cond_map_stoppedIndex_singleton_mass
    (r : ℕ) (hr : 1 ≤ r) (i : StoppedWalkIndex r) (hn : 1 ≤ i.1) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedIndex r hr) {some i} =
      (1 / 3 : ENNReal) ^ i.1 / iidCodeMeasure (boltzmannEvent r) := by
  rw [Measure.map_apply (measurable_stoppedIndex r hr)
    (measurableSet_singleton (some i)), stoppedIndex_preimage_singleton]
  have hmass : iidCodeMeasure[|boltzmannEvent r] (stoppedWalkIndexSet i) =
      (1 / 3 : ENNReal) ^ i.1 / iidCodeMeasure (boltzmannEvent r) := by
    simp only [stoppedWalkIndexSet, hn, ↓reduceIte]
    exact boltzmann_cond_stoppedCylinder_mass hr hn i.2.2
  exact hmass

/-- Full singleton law, including the zero-time indices in the ambient sigma
type. Such indices have no mass because the source stopping time is positive
on `boltzmannEvent r`. -/
theorem boltzmann_cond_map_stoppedIndex_singleton_mass_all
    (r : ℕ) (hr : 1 ≤ r) (i : StoppedWalkIndex r) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedIndex r hr) {some i} =
      if 1 ≤ i.1 then
        (1 / 3 : ENNReal) ^ i.1 / iidCodeMeasure (boltzmannEvent r)
      else 0 := by
  by_cases hn : 1 ≤ i.1
  · simp only [hn, ↓reduceIte]
    exact boltzmann_cond_map_stoppedIndex_singleton_mass r hr i hn
  · rw [Measure.map_apply (measurable_stoppedIndex r hr)
      (measurableSet_singleton (some i)), stoppedIndex_preimage_singleton]
    simp [stoppedWalkIndexSet, hn]

end DirectedDistances.KMSW
