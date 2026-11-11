module

public import DirectedDistances.Probability.BSLocalCriterion

/-! Helper toward Proposition 5.16: compare the fixed-radius class topology on a
subspace with its induced topology, and transfer local cylinder convergence.
These are supporting results, not paper results. -/

public section
namespace DirectedDistances.Probability

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ENNReal

/-- Helper toward Proposition 5.16: the local class topology agrees with the
subspace topology when class agreement is characterized by dyadic closed
balls. -/
theorem localClassTopology_eq_induced
    {X : Type*} [PseudoEMetricSpace X] {S : Set X} {C : ℕ → Type*}
    (b : ∀ r, S → C r)
    (hball : ∀ r (x y : S),
      edist (x : X) y ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔ b r x = b r y)
    (hcompat : ∀ r x y, b (r + 1) x = b (r + 1) y → b r x = b r y) :
    localClassTopology b = (inferInstance : TopologicalSpace S) := by
  classical
  apply TopologicalSpace.ext
  funext U
  apply propext
  constructor
  · intro hU
    have hle : (inferInstance : TopologicalSpace S) ≤ localClassTopology b := by
      apply le_generateFrom
      rintro t ⟨r, c, rfl⟩
      let q : ℝ≥0∞ := (1 / 2 : ℝ≥0∞) ^ (r + 1)
      have hq : 0 < q := by
        exact ENNReal.pow_pos (by norm_num) _
      apply EMetric.isOpen_iff.mpr
      intro x hx
      refine ⟨q, hq, ?_⟩
      intro y hy
      change b r x = c at hx
      have hdist : edist (x : X) y ≤ q :=
        le_of_lt (by simpa only [Metric.mem_eball, Subtype.edist_eq, edist_comm] using hy)
      have heq := (hball r x y).mp (by simpa [q] using hdist)
      exact heq.symm.trans hx
    exact hle U hU
  · intro hU
    change IsOpen[(inferInstance : TopologicalSpace S)] U at hU
    rcases isOpen_induced_iff.mp hU with ⟨W, hW, hWU⟩
    let q : ℝ≥0∞ := (1 / 2 : ℝ≥0∞)
    have hq0 : 0 < q := by norm_num [q]
    have hq1 : q < 1 := by norm_num [q]
    have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq1
    have hBasis (x : S) (hx : x ∈ U) :
        ∃ ε : ℝ≥0∞, 0 < ε ∧ Metric.eball (x : X) ε ⊆ W := by
      have hxW : (x : X) ∈ W := by
        have hxPre : x ∈ Subtype.val ⁻¹' W := by rw [hWU]; exact hx
        exact hxPre
      exact Metric.nhds_basis_eball.mem_iff.mp (hW.mem_nhds hxW)
    let ε (x : S) (hx : x ∈ U) : ℝ≥0∞ := Classical.choose (hBasis x hx)
    have hε (x : S) (hx : x ∈ U) :
        0 < ε x hx ∧ Metric.eball (x : X) (ε x hx) ⊆ W :=
      Classical.choose_spec (hBasis x hx)
    have hRadius (x : S) (hx : x ∈ U) : ∃ r : ℕ, q ^ (r + 1) < ε x hx := by
      have hev : ∀ᶠ n in atTop, q ^ n < ε x hx := hpow (Iio_mem_nhds (hε x hx).1)
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      refine ⟨N, ?_⟩
      have hdec : q ^ (N + 1) < q ^ N := by
        have hqEq : q = (2 : ℝ≥0∞)⁻¹ := by norm_num [q]
        rw [hqEq]
        rw [← ENNReal.coe_inv_two, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
          ENNReal.coe_lt_coe]
        exact (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).2
          (Nat.lt_succ_self N)
      exact hdec.trans (hN N le_rfl)
    let r (x : S) (hx : x ∈ U) : ℕ := Classical.choose (hRadius x hx)
    have hr (x : S) (hx : x ∈ U) : q ^ (r x hx + 1) < ε x hx :=
      Classical.choose_spec (hRadius x hx)
    have hsubset (x : S) (hx : x ∈ U) :
        b (r x hx) ⁻¹' {b (r x hx) x} ⊆ U := by
      intro y hy
      change b (r x hx) y = b (r x hx) x at hy
      have hdle : edist (x : X) y ≤ q ^ (r x hx + 1) :=
        (hball (r x hx) x y).2 hy.symm
      have hdlt : edist (x : X) y < ε x hx := (hdle.trans_lt (hr x hx))
      have hyW : (y : X) ∈ W := (hε x hx).2 (Metric.mem_eball'.2 hdlt)
      rw [← hWU]
      exact hyW
    letI : TopologicalSpace S := localClassTopology b
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hxC : x ∈ b (r x hx) ⁻¹' {b (r x hx) x} := by simp
    exact Filter.mem_of_superset
      ((isOpen_localCylinder b (r x hx) (b (r x hx) x)).mem_nhds hxC)
      (hsubset x hx)

/-- Helper toward Proposition 5.16: cylinder-mass convergence on a subspace
gives weak convergence there and for the push-forward to the ambient space. -/
theorem tendsto_of_localCylinder_subspace
    {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {S : Set X} {C : ℕ → Type*}
    (b : ∀ r, S → C r)
    (hball : ∀ r (x y : S),
      edist (x : X) y ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1) ↔ b r x = b r y)
    (hcompat : ∀ r x y, b (r + 1) x = b (r + 1) y → b r x = b r y)
    [∀ r, Countable (C r)] :
    letI : TopologicalSpace S := localClassTopology b
    letI : MeasurableSpace S := borel S
    letI : BorelSpace S := ⟨rfl⟩
    letI : OpensMeasurableSpace S := ⟨ge_of_eq BorelSpace.measurable_eq⟩
    ∀ {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
      {μs : ι → ProbabilityMeasure S} {μ : ProbabilityMeasure S},
      (∀ r c, Tendsto (fun i => μs i (b r ⁻¹' {c})) L
        (𝓝 (μ (b r ⁻¹' {c})))) →
      Tendsto μs L (𝓝 μ) ∧
        Tendsto (fun i => (μs i).map Subtype.val) L (𝓝 (μ.map Subtype.val)) := by
  classical
  intro ι L hL μs μ hmass
  have htop := localClassTopology_eq_induced b hball hcompat
  letI : TopologicalSpace S := localClassTopology b
  letI : MeasurableSpace S := borel S
  letI : BorelSpace S := ⟨rfl⟩
  letI : OpensMeasurableSpace S := ⟨ge_of_eq BorelSpace.measurable_eq⟩
  have hlocal : Tendsto μs L (𝓝 μ) :=
    tendsto_of_localCylinder b hcompat hmass
  have hval : @Continuous S X (localClassTopology b)
      (inferInstance : TopologicalSpace X) (Subtype.val) := by
    rw [htop]
    exact continuous_subtype_val
  refine ⟨hlocal, ?_⟩
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hlocal hval

end DirectedDistances.Probability

end
