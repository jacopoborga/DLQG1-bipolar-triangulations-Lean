module

public import DirectedDistances.Probability.SkorokhodJ1WindowSeparableSpace

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Basic

public section
namespace DirectedDistances.Probability

open Set
open scoped ENNReal Topology

private theorem exists_sparse_partition_of_modulus_lt {T : ℝ} (hT : 0 < T)
    (f : CadlagWindow T) {δ ε : ℝ} (hδT : δ < T)
    (hmod : cadlagModulus (hT := hT) f δ < ε) :
    ∃ p : WindowPartition T hT, p.IsSparse δ ∧
      ∀ i : Fin p.n,
        blockOscillation f (p.time i.castSucc) (p.time i.succ) < ε := by
  have hne : (Set.range fun p : {p : WindowPartition T hT // p.IsSparse δ} =>
      sSup (Set.range fun i : Fin p.1.n =>
        blockOscillation f (p.1.time i.castSucc) (p.1.time i.succ))).Nonempty := by
    obtain ⟨p⟩ := (windowPartition_sparse_nonempty_iff hT δ).2 hδT
    exact ⟨_, ⟨p, rfl⟩⟩
  have hinf : sInf (Set.range fun p : {p : WindowPartition T hT // p.IsSparse δ} =>
      sSup (Set.range fun i : Fin p.1.n =>
        blockOscillation f (p.1.time i.castSucc) (p.1.time i.succ))) < ε := by
    simpa only [cadlagModulus, dite_eq_left hδT] using hmod
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := exists_lt_of_csInf_lt hne hinf
  refine ⟨p.1, p.2, fun i => ?_⟩
  exact (le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩).trans_lt hp

private theorem sparse_partition_size_le {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) {δ : ℝ} (hδ : 0 < δ) (hp : p.IsSparse δ) :
    (p.n : ℝ) ≤ T / δ := by
  have hnode : ∀ i : Fin (p.n + 1), (i.val : ℝ) * δ ≤ (p.time i : ℝ) := by
    intro i
    induction i using Fin.induction with
    | zero => simp only [Fin.val_zero, Nat.cast_zero, zero_mul, p.first, Subtype.coe_mk,
        le_refl]
    | succ i ih =>
      have hg := hp i
      simp only [Fin.val_castSucc] at ih
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      nlinarith only [ih, hg]
  have hl := hnode (Fin.last p.n)
  rw [p.last] at hl
  exact (le_div_iff₀ hδ).2 hl

private theorem partition_exists_block {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (s : J1Window T) (hsT : (s : ℝ) < T) :
    ∃ i : Fin p.n, p.time i.castSucc ≤ s ∧ s < p.time i.succ := by
  classical
  let q : Finset (Fin (p.n + 1)) :=
    Finset.univ.filter fun j => (s : ℝ) < (p.time j : ℝ)
  have hq : q.Nonempty := by
    refine ⟨Fin.last p.n, ?_⟩
    simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [p.last]
    exact hsT
  let j := q.min' hq
  have hjq : j ∈ q := Finset.min'_mem q hq
  have hjs : (s : ℝ) < (p.time j : ℝ) := by
    simpa only [q, Finset.mem_filter, Finset.mem_univ, true_and] using hjq
  have hjpos : 0 < j.val := by
    by_contra hj
    have hjzero : j.val = 0 := by omega
    have htime : p.time j = p.time 0 := congrArg p.time (Fin.ext hjzero)
    rw [htime, p.first] at hjs
    exact (not_lt_of_ge s.property.1) hjs
  let i : Fin p.n := ⟨j.val - 1, by have := j.isLt; omega⟩
  have hji : i.succ = j := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp [i]
    omega
  have hleft : p.time i.castSucc ≤ s := by
    by_contra hnot
    have hprev : (s : ℝ) < (p.time i.castSucc : ℝ) := lt_of_not_ge hnot
    have hprev_mem : i.castSucc ∈ q := by
      simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hprev
    have hmin := Finset.min'_le q i.castSucc hprev_mem
    have hmin' : i.succ ≤ i.castSucc := by simpa [hji] using hmin
    have hvals : (i.succ).val ≤ (i.castSucc).val := hmin'
    simp only [Fin.val_succ, Fin.val_castSucc] at hvals
    omega
  refine ⟨i, hleft, ?_⟩
  rw [hji]
  exact hjs

private theorem compactness_adjacent_sum (n : ℕ) :
    ∀ f : Fin (n + 1) → ℝ,
      (Finset.univ.sum (fun i : Fin n => f i.succ - f i.castSucc)) =
        f (Fin.last n) - f 0 := by
  induction n with
  | zero =>
    intro f
    simp
  | succ n ih =>
    intro f
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun j => f (Fin.castSucc j))
    have hsum :
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.succ (Fin.castSucc i)) - f (Fin.castSucc (Fin.castSucc i))) =
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.castSucc (Fin.succ i)) - f (Fin.castSucc (Fin.castSucc i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show Fin.succ (Fin.castSucc i) = Fin.castSucc i.succ by
        exact Fin.ext (by simp)]
    have hfirst :
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.castSucc (Fin.succ i)) - f (Fin.castSucc (Fin.castSucc i))) =
        f (Fin.castSucc (Fin.last n)) - f 0 := by
      simpa using hih
    rw [hsum, hfirst]
    have hlast : f (Fin.last n).succ = f (Fin.last (n + 1)) := by
      congr 1
    rw [hlast]
    ring

private theorem compactness_increment_nonneg {a b s t : ℝ}
    (hab : a ≤ b) (hst : s ≤ t) :
    0 ≤ (min t b - min t a) - (min s b - min s a) := by
  by_cases hsa : s ≤ a
  · by_cases hta : t ≤ a
    · rw [min_eq_left hta, min_eq_left hsa,
        min_eq_left (le_trans hta hab), min_eq_left (le_trans hsa hab)]
      simp
    · have hat : a < t := lt_of_not_ge hta
      rw [min_eq_left hsa, min_eq_left (le_trans hsa hab), min_eq_right hat.le]
      have ham : a ≤ min t b := le_min hat.le hab
      linarith
  · have has : a < s := lt_of_not_ge hsa
    have hat : a < t := lt_of_lt_of_le has hst
    rw [min_eq_right has.le, min_eq_right hat.le]
    have hmin : min s b ≤ min t b := min_le_min hst le_rfl
    linarith

private theorem compactness_increment_sum {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) {s t : ℝ}
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    Finset.univ.sum (fun i : Fin p.n =>
      (min t (p.time i.succ : ℝ) - min t (p.time i.castSucc : ℝ)) -
        (min s (p.time i.succ : ℝ) - min s (p.time i.castSucc : ℝ))) = t - s := by
  let f : Fin (p.n + 1) → ℝ := fun j =>
    min t (p.time j : ℝ) - min s (p.time j : ℝ)
  calc
    _ = Finset.univ.sum (fun i : Fin p.n => f i.succ - f i.castSucc) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      ring
    _ = f (Fin.last p.n) - f 0 := compactness_adjacent_sum p.n f
    _ = t - s := by
      dsimp [f]
      simp only [p.last, p.first, Subtype.coe_mk]
      rw [min_eq_left htT, min_eq_left hsT,
        min_eq_right ht0, min_eq_right hs0]
      ring

private theorem compactness_slopeNorm_le
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (φ : J1TimeChange T) {A : ℝ}
    (hlog : ∀ i : Fin p.n,
      |Real.log (windowPartitionSecantSlope p φ i)| ≤ A) :
    j1TimeChangeSlopeNorm (windowPartitionInterpolantTimeChange p φ) ≤
      ENNReal.ofReal A := by
  classical
  let μ := windowPartitionInterpolantTimeChange p φ
  unfold j1TimeChangeSlopeNorm
  apply iSup_le
  intro q
  let x : J1Window T := q.1.1
  let y : J1Window T := q.1.2
  let s : ℝ := x
  let t : ℝ := y
  have hst : s < t := by exact_mod_cast q.2
  let d : Fin p.n → ℝ := fun i =>
    (min t (p.time i.succ : ℝ) - min t (p.time i.castSucc : ℝ)) -
      (min s (p.time i.succ : ℝ) - min s (p.time i.castSucc : ℝ))
  have hd (i : Fin p.n) : 0 ≤ d i := by
    apply compactness_increment_nonneg
    · exact (p.strict i).le
    · exact hst.le
  have hsum : ∑ i : Fin p.n, d i = t - s := by
    exact compactness_increment_sum p
      (by exact_mod_cast x.property.1)
      (by exact_mod_cast y.property.1)
      (by exact_mod_cast x.property.2)
      (by exact_mod_cast y.property.2)
  have hdiff :
      windowPartitionLinearInterpolant p φ y -
          windowPartitionLinearInterpolant p φ x =
        ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i := by
    rw [windowPartitionLinearInterpolant_def, windowPartitionLinearInterpolant_def,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [d, s, t]
    ring
  have hden : 0 < t - s := sub_pos.mpr hst
  have hslope_lo (i : Fin p.n) :
      Real.exp (-A) ≤ windowPartitionSecantSlope p φ i := by
    have h := abs_le.mp (hlog i)
    exact (Real.le_log_iff_exp_le (windowPartitionSecantSlope_pos p φ i)).mp h.1
  have hslope_hi (i : Fin p.n) :
      windowPartitionSecantSlope p φ i ≤ Real.exp A := by
    have h := abs_le.mp (hlog i)
    exact (Real.log_le_iff_le_exp (windowPartitionSecantSlope_pos p φ i)).mp h.2
  have hsumlo : Real.exp (-A) * (t - s) ≤
      ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i := by
    calc
      Real.exp (-A) * (t - s) =
          ∑ i : Fin p.n, Real.exp (-A) * d i := by rw [← hsum, Finset.mul_sum]
      _ ≤ ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hslope_lo i) (hd i)
  have hsumhi :
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) ≤
        Real.exp A * (t - s) := by
    calc
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) ≤
          ∑ i : Fin p.n, Real.exp A * d i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hslope_hi i) (hd i)
      _ = Real.exp A * (t - s) := by rw [← Finset.mul_sum, hsum]
  have hnumpos :
      0 < ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hden) hsumlo
  have hratio_lo : Real.exp (-A) ≤
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s) :=
    (le_div_iff₀ hden).2 hsumlo
  have hratio_hi :
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s) ≤
        Real.exp A := (div_le_iff₀ hden).2 hsumhi
  have hratio_pos : 0 <
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s) :=
    div_pos hnumpos hden
  have hloglo : -A ≤ Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s)) :=
    (Real.le_log_iff_exp_le hratio_pos).2 hratio_lo
  have hloghi : Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s)) ≤ A :=
    (Real.log_le_iff_le_exp hratio_pos).2 hratio_hi
  have hlogabs : |Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s))| ≤ A :=
    abs_le.mpr ⟨hloglo, hloghi⟩
  have hchord : j1ChordLogSlope μ q = Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s)) := by
    change Real.log (((μ y : ℝ) - (μ x : ℝ)) / (t - s)) = _
    rw [windowPartitionInterpolantTimeChange_apply,
      windowPartitionInterpolantTimeChange_apply, hdiff]
  rw [hchord]
  exact ENNReal.ofReal_le_ofReal hlogabs

/-- nearby sparse partition nodes have an alignment with controlled logarithmic slope
(Billingsley 1999, Thm 12.3); not the paper result. -/
theorem exists_sparse_nodeTimeChange_slopeNorm_le {T : ℝ} (hT : 0 < T)
    (p : WindowPartition T hT)
    (s : Fin (p.n + 1) → Set.Icc (0 : ℝ) T)
    (hsfirst : s 0 = ⟨0, by simp [hT.le]⟩)
    (hslast : s (Fin.last p.n) = ⟨T, hT.le, le_rfl⟩)
    (hsstrict : ∀ i : Fin p.n, (s i.castSucc).val < (s i.succ).val)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hsmall : 4 * η ≤ δ)
    (hsparse : ∀ i : Fin p.n, δ < (s i.succ : ℝ) - (s i.castSucc : ℝ))
    (hclose : ∀ i, |(s i : ℝ) - (p.time i : ℝ)| ≤ η) :
    ∃ φ : J1TimeChange T, (∀ i, φ (s i) = p.time i) ∧
      j1TimeChangeSlopeNorm φ ≤ ENNReal.ofReal (4 * (η / δ)) := by
  classical
  let q : WindowPartition T hT :=
    { n := p.n, n_pos := p.n_pos, time := s, first := hsfirst,
      last := hslast, strict := hsstrict }
  obtain ⟨ψ, hnodes, hdisp⟩ := exists_windowPartition_nodeTimeChange hT p s
    hsfirst hslast hsstrict
  have hmax : Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (p.n + 1) => |(s i : ℝ) - (p.time i : ℝ)|) ≤ η := by
    exact Finset.sup'_le _ _ (fun i _ => hclose i)
  let φ := windowPartitionInterpolantTimeChange q ψ
  refine ⟨φ, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    rw [windowPartitionInterpolantTimeChange_apply]
    exact (windowPartitionLinearInterpolant_node q ψ i).trans
      (congrArg Subtype.val (hnodes i))
  · apply compactness_slopeNorm_le
    intro i
    exact windowPartitionSecantSlope_log_abs_le q ψ hδ hη hsmall
      (fun t => (hdisp t).trans hmax) hsparse i

private theorem block_error_le {T : ℝ} (x : CadlagWindow T)
    (a b t : J1Window T) {ω : ℝ} (hab : a < b)
    (hl : a ≤ t) (hr : t < b) (h : blockOscillation x a b ≤ ω) :
    |x.1 t - x.1 a| ≤ ω := by
  apply le_trans (le_csSup (blockOscillation_values_bddAbove x a b) ?_) h
  exact ⟨t, a, hl, hr, le_rfl, hab, rfl⟩

private theorem aligned_partition_dCirc_le {T : ℝ} (hT : 0 < T)
    (x y : CadlagWindow T) (p : WindowPartition T hT)
    (s : Fin (p.n + 1) → Set.Icc (0 : ℝ) T)
    (hsfirst : s 0 = ⟨0, by simp [hT.le]⟩)
    (hslast : s (Fin.last p.n) = ⟨T, hT.le, le_rfl⟩)
    (hsstrict : ∀ i : Fin p.n, (s i.castSucc).val < (s i.succ).val)
    {δ η ω ν : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hω : 0 ≤ ω)
    (hsmall : 4 * η ≤ δ)
    (hsparse : ∀ i : Fin p.n, δ < (s i.succ : ℝ) - (s i.castSucc : ℝ))
    (hclose : ∀ i, |(s i : ℝ) - (p.time i : ℝ)| ≤ η)
    (hoscx : ∀ i : Fin p.n,
      blockOscillation x (p.time i.castSucc) (p.time i.succ) ≤ ω)
    (hoscy : ∀ i : Fin p.n, blockOscillation y (s i.castSucc) (s i.succ) ≤ ω)
    (hvalues : ∀ i, |x.1 (p.time i) - y.1 (s i)| ≤ ν) :
    j1WindowDCirc hT x y ≤ ENNReal.ofReal (max (4 * (η / δ)) (2 * ω + ν)) := by
  let : Nonempty (J1Window T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  obtain ⟨φ, hnodes, hnorm⟩ := exists_sparse_nodeTimeChange_slopeNorm_le hT p s
    hsfirst hslast hsstrict hδ hη hsmall hsparse hclose
  let q : WindowPartition T hT :=
    { n := p.n, n_pos := p.n_pos, time := s, first := hsfirst,
      last := hslast, strict := hsstrict }
  have hpoint (t : J1Window T) : |x.1 (φ t) - y.1 t| ≤ 2 * ω + ν := by
    by_cases ht : (t : ℝ) = T
    · have ht' : t = s (Fin.last p.n) := by rw [hslast]; exact Subtype.ext ht
      rw [ht', hnodes]
      exact (hvalues _).trans (by linarith only [hω])
    · obtain ⟨i, hl, hr⟩ := partition_exists_block q t (lt_of_le_of_ne t.property.2 ht)
      have hl' : p.time i.castSucc ≤ φ t := by
        rw [← hnodes]
        exact φ.monotone hl
      have hr' : φ t < p.time i.succ := by
        rw [← hnodes]
        exact φ.strictMono hr
      have hx := block_error_le x _ _ (φ t) (p.strict i) hl' hr' (hoscx i)
      have hy := block_error_le y _ _ t (hsstrict i) hl hr (hoscy i)
      have hv := hvalues i.castSucc
      calc
        |x.1 (φ t) - y.1 t| ≤
            |x.1 (φ t) - x.1 (p.time i.castSucc)| +
              |x.1 (p.time i.castSucc) - y.1 t| := abs_sub_le _ _ _
        _ ≤ |x.1 (φ t) - x.1 (p.time i.castSucc)| +
            (|x.1 (p.time i.castSucc) - y.1 (s i.castSucc)| +
              |y.1 (s i.castSucc) - y.1 t|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ ≤ ω + (ν + ω) := by
          rw [abs_sub_comm (y.1 (s i.castSucc)) (y.1 t)]
          exact add_le_add hx (add_le_add hv hy)
        _ = 2 * ω + ν := by ring
  have hsup : (⨆ t : J1Window T, |x.1 (φ t) - y.1 t|) ≤ 2 * ω + ν := by
    apply ciSup_le
    exact hpoint
  have hcost : j1WindowDCircCost x y φ ≤
      ENNReal.ofReal (max (4 * (η / δ)) (2 * ω + ν)) := by
    apply max_le
    · exact hnorm.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact ENNReal.ofReal_le_ofReal (hsup.trans (le_max_right _ _))
  exact (iInf_le (fun ψ : J1TimeChange T => j1WindowDCircCost x y ψ) φ).trans hcost

private noncomputable def bounded_interval_code (R η : ℝ) (hη : 0 < η)
    (x : ℝ) (hx : |x| ≤ R) : Set.Icc (Int.floor (-R / η)) (Int.floor (R / η)) :=
  ⟨Int.floor (x / η),
    Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hx).1 hη.le),
    Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hx).2 hη.le)⟩

private theorem bounded_interval_code_close (R η : ℝ) (hη : 0 < η)
    (x y : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R)
    (h : bounded_interval_code R η hη x hx = bounded_interval_code R η hη y hy) :
    |x - y| < η := by
  have hf : Int.floor (x / η) = Int.floor (y / η) := congrArg Subtype.val h
  have he := Int.abs_sub_lt_one_of_floor_eq_floor hf
  rw [← sub_div, abs_div, abs_of_pos hη] at he
  exact (div_lt_iff₀ hη).1 he |>.trans_eq (one_mul η)

private theorem totallyBounded_circ_of_bdd_sup_modulus {T : ℝ} (hT : 0 < T)
    (A : Set (J1WindowCirc T hT))
    (hsup : ∃ M, ∀ f ∈ A, ∀ t, |(ofJ1WindowCirc hT f).1 t| ≤ M)
    (hmod : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∀ f ∈ A, cadlagModulus (hT := hT) (ofJ1WindowCirc hT f) δ ≤ ε) :
    TotallyBounded A := by
  classical
  obtain ⟨M, hM⟩ := hsup
  let path (f : A) := ofJ1WindowCirc hT f.val
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  obtain ⟨δ, hδ, hδT, hmodδ⟩ := hmod (ε / 8) (by positivity)
  have hpart (f : A) : ∃ p : WindowPartition T hT, p.IsSparse δ ∧
      ∀ i : Fin p.n,
        blockOscillation (path f) (p.time i.castSucc) (p.time i.succ) < ε / 4 := by
    apply exists_sparse_partition_of_modulus_lt hT (path f) hδT
    exact (hmodδ f.val f.property).trans_lt (by linarith only [hε])
  choose p hsp hosc using hpart
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  have hn (f : A) : (p f).n < N := by
    exact_mod_cast (sparse_partition_size_le (p f) hδ (hsp f)).trans_lt hN
  let η := min (δ / 8) (min (ε * δ / 16) (ε / 8))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η ≤ δ / 8 := min_le_left _ _
  have hηεδ : η ≤ ε * δ / 16 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : 4 * η ≤ δ := by linarith only [hηδ, hδ]
  have hnorm : 4 * (η / δ) ≤ ε / 4 := by
    rw [show 4 * (η / δ) = (4 * η) / δ by ring]
    apply (div_le_iff₀ hδ).2
    nlinarith only [hηεδ]
  have hbound : max (4 * (η / δ)) (2 * (ε / 4) + η) < ε := by
    exact max_lt_iff.mpr ⟨hnorm.trans_lt (by linarith only [hε]),
      by linarith only [hηε, hε]⟩
  let R := max T M
  let node (f : A) (k : ℕ) : J1Window T :=
    (p f).time ⟨min k (p f).n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hnode (f : A) (i : Fin ((p f).n + 1)) : node f i.val = (p f).time i := by
    apply congrArg (p f).time
    apply Fin.ext
    exact min_eq_left (by omega)
  have htbound (f : A) (k : ℕ) : |(node f k : ℝ)| ≤ R := by
    rw [abs_of_nonneg (node f k).property.1]
    exact (node f k).property.2.trans (le_max_left _ _)
  have hvbound (f : A) (k : ℕ) : |(path f).1 (node f k)| ≤ R :=
    (hM f.val f.property _).trans (le_max_right _ _)
  let C := Set.Icc (Int.floor (-R / η)) (Int.floor (R / η))
  let β := Fin (N + 1) × (Fin (N + 1) → C × C)
  let F : A → β := fun f =>
    (⟨(p f).n, by have := hn f; omega⟩, fun j =>
      (bounded_interval_code R η hη (node f j.val) (htbound f j.val),
        bounded_interval_code R η hη ((path f).1 (node f j.val)) (hvbound f j.val)))
  refine ⟨β, inferInstance, F, ?_⟩
  intro f g hfg
  have hnfg : (p f).n = (p g).n := congrArg (fun c : β => c.1.val) hfg
  let s : Fin ((p f).n + 1) → J1Window T := fun i => node g i.val
  have hsg (i : Fin ((p f).n + 1)) :
      s i = (p g).time ⟨i.val, by have := i.isLt; omega⟩ :=
    hnode g ⟨i.val, by have := i.isLt; omega⟩
  have hsfirst : s 0 = ⟨0, by simp [hT.le]⟩ :=
    (hnode g 0).trans (p g).first
  have hslast : s (Fin.last (p f).n) = ⟨T, hT.le, le_rfl⟩ := by
    change node g (p f).n = _
    rw [hnfg]
    exact (hnode g (Fin.last (p g).n)).trans (p g).last
  have hsgap (i : Fin (p f).n) : δ < (s i.succ : ℝ) - (s i.castSucc : ℝ) := by
    rw [hsg, hsg]
    exact hsp g ⟨i.val, by have := i.isLt; omega⟩
  have hsstrict (i : Fin (p f).n) : (s i.castSucc : ℝ) < (s i.succ : ℝ) := by
    have := hsgap i
    linarith only [this, hδ]
  have hoscy (i : Fin (p f).n) :
      blockOscillation (path g) (s i.castSucc) (s i.succ) ≤ ε / 4 := by
    rw [hsg, hsg]
    exact (hosc g ⟨i.val, by have := i.isLt; omega⟩).le
  have htime (i : Fin ((p f).n + 1)) :
      |((p f).time i : ℝ) - (s i : ℝ)| < η := by
    let j : Fin (N + 1) := ⟨i.val, by have := hn f; have := i.isLt; omega⟩
    have heq := congrArg (fun c : β => (c.2 j).1) hfg
    have he := bounded_interval_code_close R η hη
      (node f j.val) (node g j.val) (htbound f j.val) (htbound g j.val) heq
    simpa only [j, hnode f i] using he
  have hvalue (i : Fin ((p f).n + 1)) :
      |(path f).1 ((p f).time i) - (path g).1 (s i)| < η := by
    let j : Fin (N + 1) := ⟨i.val, by have := hn f; have := i.isLt; omega⟩
    have heq := congrArg (fun c : β => (c.2 j).2) hfg
    have he := bounded_interval_code_close R η hη
      ((path f).1 (node f j.val)) ((path g).1 (node g j.val))
      (hvbound f j.val) (hvbound g j.val) heq
    simpa only [j, hnode f i] using he
  have hd := aligned_partition_dCirc_le hT (path f) (path g) (p f) s
    hsfirst hslast hsstrict hδ hη.le (by positivity : 0 ≤ ε / 4) hsmall hsgap
    (fun i => by rw [abs_sub_comm]; exact (htime i).le)
    (fun i => (hosc f i).le) hoscy (fun i => (hvalue i).le)
  rw [j1WindowCirc_dist_eq]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr.trans_lt hbound

/-- uniform sup bounds and a uniform sparse modulus give total boundedness in d°
(Billingsley 1999, Thm 12.3); not the paper result. -/
theorem totallyBounded_j1WindowDToCirc_of_bdd_sup_modulus {T : ℝ} (hT : 0 < T)
    (A : Set (J1WindowD T hT))
    (hsup : ∃ M, ∀ f ∈ A, ∀ t, |f.path.1 t| ≤ M)
    (hmod : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∀ f ∈ A, cadlagModulus (hT := hT) f.path δ ≤ ε) :
    TotallyBounded (j1WindowDToCirc hT '' A) := by
  apply totallyBounded_circ_of_bdd_sup_modulus hT
  · obtain ⟨M, hM⟩ := hsup
    refine ⟨M, ?_⟩
    rintro _ ⟨f, hf, rfl⟩ t
    exact hM f hf t
  · intro ε hε
    obtain ⟨δ, hδ, hδT, hd⟩ := hmod ε hε
    refine ⟨δ, hδ, hδT, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact hd f hf

/-- uniform sup bounds and a uniform sparse modulus give a compact J1 closure
(Billingsley 1999, Thm 12.3); not the paper result. -/
theorem isCompact_closure_of_bdd_sup_modulus {T : ℝ} (hT : 0 < T)
    (A : Set (J1WindowD T hT))
    (hsup : ∃ M, ∀ f ∈ A, ∀ t, |f.path.1 t| ≤ M)
    (hmod : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧
      ∀ f ∈ A, cadlagModulus (hT := hT) f.path δ ≤ ε) :
    IsCompact (closure A) := by
  let e := j1WindowCircHomeomorphD hT
  have htb := totallyBounded_j1WindowDToCirc_of_bdd_sup_modulus hT A hsup hmod
  have hc : IsCompact (closure (j1WindowDToCirc hT '' A)) :=
    htb.closure.isCompact_of_isClosed isClosed_closure
  have hi := hc.image e.continuous
  rw [e.image_closure] at hi
  have he : e '' (j1WindowDToCirc hT '' A) = A := by
    ext f
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact hg
    · intro hf
      exact ⟨j1WindowDToCirc hT f, ⟨f, hf, rfl⟩, rfl⟩
  rw [he] at hi
  exact hi

end DirectedDistances.Probability
