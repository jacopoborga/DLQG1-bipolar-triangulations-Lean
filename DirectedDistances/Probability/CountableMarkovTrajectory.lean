module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Algebra.BigOperators.Fin

/-! # Countable-state Markov trajectories

Generic Ionescu–Tulcea infrastructure for the conditioned trajectory construction
No numbered paper result is asserted here. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open Finset Preorder
open scoped ENNReal Classical

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]

/-- History kernel of a time-homogeneous chain: only the current state matters. -/
@[expose] noncomputable def markovHistoryKernel (κ : Kernel S S) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → S) S where
  toFun p := κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := measurable_of_countable _

theorem markovHistoryKernel_apply (κ : Kernel S S) (n : ℕ)
    (p : (i : Finset.Iic n) → S) :
    markovHistoryKernel κ n p = κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := rfl

instance (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovHistoryKernel κ n) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure (κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩))
    infer_instance

/-- The actual infinite trajectory started from `s`. -/
@[expose] noncomputable def markovTrajectory (κ : Kernel S S) [IsMarkovKernel κ]
    (s : S) : Measure (ℕ → S) :=
  Kernel.traj (X := fun _ => S) (markovHistoryKernel κ) 0 (fun _ => s)

instance (κ : Kernel S S) [IsMarkovKernel κ] (s : S) :
    IsProbabilityMeasure (markovTrajectory κ s) := by
  unfold markovTrajectory
  infer_instance

private theorem markovTrajectory_map_prefix (κ : Kernel S S) [IsMarkovKernel κ]
    (s : S) (n : ℕ) :
    (markovTrajectory κ s).map (Finset.Iic n).restrict =
      Kernel.partialTraj (X := fun _ => S) (markovHistoryKernel κ) 0 n (fun _ => s) := by
  exact Kernel.traj_map_frestrictLe_apply (X := fun _ => S) 0 n (fun _ => s)

private theorem markovTrajectory_prefix_atom (κ : Kernel S S) [IsMarkovKernel κ]
    (s : S) (n : ℕ) (q : (i : Finset.Iic n) → S) :
    markovTrajectory κ s {p | (Finset.Iic n).restrict p = q} =
      Kernel.partialTraj (X := fun _ => S) (markovHistoryKernel κ) 0 n (fun _ => s) {q} := by
  rw [← markovTrajectory_map_prefix κ s n,
    Measure.map_apply (by fun_prop) (measurableSet_singleton q)]
  rfl

omit [MeasurableSingletonClass S] [Countable S] in
private theorem append_history_eq_iff (n : ℕ)
    (p : (i : Finset.Iic n) → S) (y : S)
    (q : (i : Finset.Iic (n + 1)) → S) :
    _root_.IicProdIoc (X := fun _ => S) n (n + 1) (p, MeasurableEquiv.piSingleton (X := fun _ => S) n y) = q ↔
      p = frestrictLe₂ (π := fun _ => S) (Nat.le_succ n) q ∧
        y = q ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
  have hhead : frestrictLe₂ (π := fun _ => S) (Nat.le_succ n)
      (_root_.IicProdIoc (X := fun _ => S) n (n + 1) (p, MeasurableEquiv.piSingleton (X := fun _ => S) n y)) = p := by
    exact congrFun (frestrictLe₂_comp_IicProdIoc (X := fun _ => S) (Nat.le_succ n))
      (p, MeasurableEquiv.piSingleton (X := fun _ => S) n y)
  have hlast : _root_.IicProdIoc (X := fun _ => S) n (n + 1) (p, MeasurableEquiv.piSingleton (X := fun _ => S) n y)
      ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ = y := by
    simp [_root_.IicProdIoc, MeasurableEquiv.piSingleton]
  constructor
  · intro h
    exact ⟨hhead.symm.trans (congrArg (frestrictLe₂ (π := fun _ => S) (Nat.le_succ n)) h),
      hlast.symm.trans (congrArg (fun r => r ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) h)⟩
  · rintro ⟨rfl, rfl⟩
    funext i
    by_cases hi : i.val ≤ n
    · simp [_root_.IicProdIoc, hi, frestrictLe₂_apply]
    · have hieq : i.val = n + 1 := by
        have := Finset.mem_Iic.mp i.property
        omega
      have hiend : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hieq
      subst i
      exact hlast

/-- An actual one-step extension has exactly its transition mass when the
previous coordinates match, and mass zero otherwise. -/
private theorem markovPartialTraj_succ_singleton (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ)
    (p : (i : Finset.Iic n) → S)
    (q : (i : Finset.Iic (n + 1)) → S) :
    Kernel.partialTraj (X := fun _ => S) (markovHistoryKernel κ) n (n + 1) p {q} =
      if p = frestrictLe₂ (π := fun _ => S) (Nat.le_succ n) q then
        κ (p ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          {q ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩} else 0 := by
  classical
  rw [Kernel.partialTraj_succ_self,
    Kernel.map_apply' _ (by fun_prop) _ (measurableSet_singleton q),
    Kernel.id_prod_apply' _ _ ((measurableSet_singleton q).preimage (by fun_prop)),
    Kernel.map_apply' _ (MeasurableEquiv.piSingleton (X := fun _ => S) n).measurable]
  · by_cases hp : p = frestrictLe₂ (π := fun _ => S) (Nat.le_succ n) q
    · rw [ite_eq_left hp]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, append_history_eq_iff, hp,
        true_and]
    · rw [ite_eq_right hp]
      have he :
          (MeasurableEquiv.piSingleton (X := fun _ => S) n) ⁻¹'
            (Prod.mk p ⁻¹' (_root_.IicProdIoc (X := fun _ => S) n (n + 1) ⁻¹' {q})) = ∅ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, append_history_eq_iff, hp,
          false_and, Set.mem_empty_iff_false]
      rw [he, measure_empty]
  · exact ((measurableSet_singleton q).preimage (by fun_prop)).preimage
      (measurable_const.prodMk measurable_id)

/-- Genuine finite-prefix atom recursion, obtained by integration of the
one-step extension; the point mass is not an assumed path-law premise. -/
private theorem markovPartialTraj_prefix_succ (κ : Kernel S S) [IsMarkovKernel κ] (x : S) (n : ℕ) (p : ℕ → S) :
    Kernel.partialTraj (X := fun _ => S) (markovHistoryKernel κ) 0 (n + 1) (fun _ => x)
        {frestrictLe (n + 1) p} =
      κ (p n) {p (n + 1)} *
        Kernel.partialTraj (X := fun _ => S) (markovHistoryKernel κ) 0 n (fun _ => x)
          {frestrictLe n p} := by
  classical
  rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),
    Kernel.comp_apply' _ _ _ (measurableSet_singleton _)]
  simp_rw [markovPartialTraj_succ_singleton]
  have hrestrict : frestrictLe₂ (π := fun _ => S) (Nat.le_succ n) (frestrictLe (n + 1) p) =
      frestrictLe n p := rfl
  simp only [hrestrict, frestrictLe_apply]
  have he :
      (fun r : (i : Finset.Iic n) → S =>
        if r = frestrictLe n p then
          κ (r ⟨n, Finset.mem_Iic.mpr le_rfl⟩) {p (n + 1)} else 0) =
      ({frestrictLe n p} : Set ((i : Finset.Iic n) → S)).indicator
        (fun _ => κ (p n) {p (n + 1)}) := by
    funext r
    by_cases hr : r = frestrictLe n p
    · subst r
      simp
    · simp [hr]
  rw [he, lintegral_indicator_const (measurableSet_singleton _)]

/-- Actual all-start finite trajectory atoms have the product of their true
transition probabilities, with zero mass for an incorrect initial state. -/
private theorem markovTrajectory_prefix_atom_mass (κ : Kernel S S) [IsMarkovKernel κ] (x : S) (n : ℕ) (p : ℕ → S) :
    markovTrajectory κ x {r | frestrictLe n r = frestrictLe n p} =
      if p 0 = x then
        ∏ i ∈ Finset.range n, κ (p i) {p (i + 1)} else 0 := by
  classical
  change markovTrajectory κ x
    {r | (Finset.Iic n).restrict r = (Finset.Iic n).restrict p} = _
  rw [markovTrajectory_prefix_atom]
  change Kernel.partialTraj (X := fun _ => S) (markovHistoryKernel κ) 0 n
    (fun _ => x) {frestrictLe n p} = _
  induction n with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_apply,
      Measure.dirac_apply' _ (measurableSet_singleton _)]
    have hp : (fun _ : Finset.Iic 0 => x) = frestrictLe 0 p ↔ p 0 = x := by
      constructor
      · intro h
        exact (congrFun h ⟨0, by simp⟩).symm
      · intro h
        funext i
        have hi : i.val = 0 := by
          have := Finset.mem_Iic.mp i.property
          omega
        simp [frestrictLe_apply, hi, h]
    simp only [Set.indicator_apply, Set.mem_singleton_iff, hp, Finset.range_zero, Finset.prod_empty, Pi.one_apply]
  | succ n ih =>
    rw [markovPartialTraj_prefix_succ, ih]
    by_cases hp : p 0 = x
    · simp only [hp, ↓reduceIte, Finset.prod_range_succ]
      exact mul_comm _ _
    · simp only [hp, ↓reduceIte, mul_zero]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] in
/-- Prefix events can be expressed as equality of finite restrictions. -/
private theorem prefix_set_eq (n : ℕ) (p : ℕ → S) :
    {r | ∀ i ≤ n, r i = p i} = {r | frestrictLe n r = frestrictLe n p} := by
  ext r
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.property)
  · intro h i hi
    exact congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩

/-- Every finite prefix has its initial-state indicator times its transition product. -/
theorem markovTrajectory_prefix_mass (κ : Kernel S S) [IsMarkovKernel κ]
    (s : S) (n : ℕ) (p : ℕ → S) :
    markovTrajectory κ s {r | ∀ i ≤ n, r i = p i} =
      if p 0 = s then ∏ i ∈ Finset.range n, κ (p i) {p (i + 1)} else 0 := by
  rw [prefix_set_eq, markovTrajectory_prefix_atom_mass]

/-- The finite vector marginal has the corresponding product singleton mass. -/
theorem markovTrajectory_map_fin_prefix_singleton (κ : Kernel S S) [IsMarkovKernel κ]
    (s : S) (n : ℕ) (q : Fin (n + 1) → S) :
    ((markovTrajectory κ s).map (fun r => fun j : Fin (n + 1) => r j.val)) {q} =
      if q 0 = s then ∏ i : Fin n, κ (q i.castSucc) {q i.succ} else 0 := by
  classical
  let p : ℕ → S := fun i => q ⟨min i n, by omega⟩
  have hp (i : ℕ) (hi : i ≤ n) : p i = q ⟨i, by omega⟩ := by
    simp only [p, min_eq_left hi]
  have he : (fun r : ℕ → S => fun j : Fin (n + 1) => r j.val) ⁻¹' {q} =
      {r | ∀ i ≤ n, r i = p i} := by
    ext r
    change (fun j : Fin (n + 1) => r j.val) = q ↔ _
    constructor
    · intro h i hi
      rw [hp i hi]
      exact congrFun h ⟨i, by omega⟩
    · intro h
      funext j
      exact (h j.val (by omega)).trans (hp j.val (by omega))
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton q), he,
    markovTrajectory_prefix_mass, Finset.prod_range]
  have hprod : (∏ i : Fin n, κ (p i) {p (i + 1)}) =
      ∏ i : Fin n, κ (q i.castSucc) {q i.succ} := by
    apply Finset.prod_congr rfl
    intro i _
    rw [hp i (by omega), hp (i + 1) (by omega)]
    rfl
  rw [hprod, hp 0 (Nat.zero_le n)]
  rfl

/-- The trajectory has its prescribed starting state almost surely. -/
theorem markovTrajectory_ae_start (κ : Kernel S S) [IsMarkovKernel κ] (s : S) :
    ∀ᵐ r ∂markovTrajectory κ s, r 0 = s := by
  have hp := markovTrajectory_map_prefix κ s 0
  have heval : (fun p : ℕ → S => p 0) =
      (fun p : (i : Finset.Iic 0) → S => p ⟨0, by simp⟩) ∘
        (Finset.Iic 0).restrict := rfl
  have hz : (markovTrajectory κ s).map (fun p => p 0) = Measure.dirac s := by
    rw [heval, ← Measure.map_map (measurable_pi_apply _) (by fun_prop), hp,
      Kernel.partialTraj_self, Kernel.id_apply,
      Measure.map_dirac' (measurable_pi_apply _)]
  have ha : ∀ᵐ z ∂Measure.dirac s, z = s := by simp
  rw [← hz] at ha
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
    (measurableSet_singleton s)).mp ha

/-- All transitions along the actual infinite trajectory have nonzero mass almost surely. -/
theorem markovTrajectory_ae_step (κ : Kernel S S) [IsMarkovKernel κ] (s : S) :
    ∀ᵐ r ∂markovTrajectory κ s, ∀ i, κ (r i) {r (i + 1)} ≠ 0 := by
  classical
  apply ae_all_iff.mpr
  intro i
  let P (q : (j : Finset.Iic (i + 1)) → S) : Prop :=
    κ (q ⟨i, Finset.mem_Iic.mpr (by omega)⟩)
      {q ⟨i + 1, Finset.mem_Iic.mpr le_rfl⟩} ≠ 0
  have ha : ∀ᵐ q ∂(markovTrajectory κ s).map (frestrictLe (i + 1)), P q := by
    apply ae_iff_of_countable.mpr
    intro q hq
    by_contra hP
    let p : ℕ → S := fun j => if hj : j ≤ i + 1 then
      q ⟨j, Finset.mem_Iic.mpr hj⟩ else s
    have hrestrict : frestrictLe (i + 1) p = q := by
      funext j
      simp only [frestrictLe_apply, p, dite_eq_left (Finset.mem_Iic.mp j.property)]
    have hbad : κ (p i) {p (i + 1)} = 0 := by
      simpa only [P, not_not, p, dite_eq_left (by omega : i ≤ i + 1),
        dite_eq_left (le_rfl : i + 1 ≤ i + 1)] using hP
    apply hq
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton q), ← hrestrict]
    change markovTrajectory κ s {r | frestrictLe (i + 1) r = frestrictLe (i + 1) p} = 0
    rw [markovTrajectory_prefix_atom_mass]
    split_ifs
    · exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self i)) hbad
    · rfl
  have hm : MeasurableSet {q : (j : Finset.Iic (i + 1)) → S | P q} :=
    (Set.to_countable _).measurableSet
  exact (ae_map_iff (by fun_prop) hm).mp ha

end DirectedDistances.Probability
