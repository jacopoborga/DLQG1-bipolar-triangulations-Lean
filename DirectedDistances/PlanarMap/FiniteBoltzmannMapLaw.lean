/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.KMSWMapIsoClass
public import DirectedDistances.PlanarMap.FiniteXDPSelectorPath
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

public section
namespace DirectedDistances.PlanarMap

open MeasureTheory
open scoped ENNReal

/-! Helpers toward `lem-lr-ind` / `def-boltzmann-lr`
and these are not the paper result. -/

/-- The unrooted map-class space over all total edge counts, including the
one-edge class at boundary lengths `(1,1)` (`def-boltzmann-lr`, -/
@[expose] noncomputable def BoltzmannSpace (ℓ r : ℕ) :=
  Σ n : ℕ, KMSWMapIsoClass ℓ r n

noncomputable instance (ℓ r : ℕ) : MeasurableSpace (BoltzmannSpace ℓ r) := ⊤

private instance (ℓ r n : ℕ) : Finite (KMSWMapIsoClass ℓ r n) :=
  KMSWMapIsoClass.finite ℓ r n

private noncomputable instance (ℓ r n : ℕ) : Fintype (KMSWMapIsoClass ℓ r n) :=
  Fintype.ofFinite _

private noncomputable instance (ℓ r n : ℕ) : Encodable (KMSWMapIsoClass ℓ r n) :=
  Encodable.ofCountable _

noncomputable instance (ℓ r : ℕ) : Encodable (BoltzmannSpace ℓ r) := by
  classical
  haveI : ∀ n, Finite (KMSWMapIsoClass ℓ r n) := fun n =>
    KMSWMapIsoClass.finite ℓ r n
  haveI : ∀ n, Encodable (KMSWMapIsoClass ℓ r n) := fun n =>
    Encodable.ofCountable _
  change Encodable (Σ n : ℕ, KMSWMapIsoClass ℓ r n)
  exact @Sigma.encodable ℕ (fun n => KMSWMapIsoClass ℓ r n)
    inferInstance (fun n => Encodable.ofCountable (KMSWMapIsoClass ℓ r n))

instance (ℓ r : ℕ) : Countable (BoltzmannSpace ℓ r) := Encodable.countable

/-- Boltzmann weight by total edge count (`def-boltzmann-lr`, -/
@[expose] noncomputable def boltzmannWeight {ℓ r : ℕ}
    (ω : BoltzmannSpace ℓ r) : ℝ≥0∞ :=
  (1 / 3 : ℝ≥0∞) ^ ω.1

/-- The unnormalized total Boltzmann weight on unrooted maps of boundary -/
@[expose] noncomputable def boltzmannPartition (ℓ r : ℕ) : ℝ≥0∞ :=
  ∑' ω : BoltzmannSpace ℓ r, boltzmannWeight ω

/-- Decompose the partition sum by total edge count, using finiteness of each
fixed-size isomorphism-class fiber. -/
theorem boltzmannPartition_eq (ℓ r : ℕ) :
    boltzmannPartition ℓ r =
      ∑' n : ℕ, (Nat.card (KMSWMapIsoClass ℓ r n) : ℝ≥0∞) *
        (1 / 3 : ℝ≥0∞) ^ n := by
  classical
  change (∑' ω : Σ n : ℕ, KMSWMapIsoClass ℓ r n,
      (1 / 3 : ℝ≥0∞) ^ ω.1) = _
  rw [tsum_sigma']
  apply tsum_congr
  intro n
  simp [Nat.card_eq_fintype_card, Finset.sum_const, nsmul_eq_mul]

/-- The normalized finite Boltzmann map law. The nonzero and finite
normalizer facts are explicit inputs here; they are not assumed as part of
this helper toward `lem-lr-ind` / `def-boltzmann-lr` -/
@[expose] noncomputable def boltzmannLaw (ℓ r : ℕ)
    (_h0 : boltzmannPartition ℓ r ≠ 0)
    (_htop : boltzmannPartition ℓ r ≠ ⊤) : Measure (BoltzmannSpace ℓ r) :=
  (boltzmannPartition ℓ r)⁻¹ •
    Measure.sum (fun ω => boltzmannWeight ω • Measure.dirac ω)

instance boltzmannLaw_isProbabilityMeasure (ℓ r : ℕ)
    (h0 : boltzmannPartition ℓ r ≠ 0)
    (htop : boltzmannPartition ℓ r ≠ ⊤) :
    IsProbabilityMeasure (boltzmannLaw ℓ r h0 htop) where
  measure_univ := by
    rw [boltzmannLaw, Measure.smul_apply, smul_eq_mul,
      Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ MeasurableSet.univ]
    simp only [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
    change (boltzmannPartition ℓ r)⁻¹ *
      (∑' ω : BoltzmannSpace ℓ r, boltzmannWeight ω) = 1
    rw [← boltzmannPartition]
    exact ENNReal.inv_mul_cancel h0 htop

/-- The atom of the normalized law has weight `3^{-n}/C_{ℓ,r}`. This
helper toward `def-boltzmann-lr` takes normalizer nonzero and finiteness as
explicit arguments and is not the paper result -/
theorem boltzmannLaw_singleton (ℓ r : ℕ)
    (h0 : boltzmannPartition ℓ r ≠ 0)
    (htop : boltzmannPartition ℓ r ≠ ⊤) (ω : BoltzmannSpace ℓ r) :
    boltzmannLaw ℓ r h0 htop {ω} =
      (1 / 3 : ℝ≥0∞) ^ ω.1 / boltzmannPartition ℓ r := by
  rw [boltzmannLaw, Measure.smul_apply,
    smul_eq_mul, Measure.sum_smul_dirac_singleton]
  simp only [boltzmannWeight]
  simp only [div_eq_mul_inv]
  exact mul_comm _ _

private noncomputable def BipolarBoundaryBaseIso.transportPath
    {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    SimpleDirectedDartPath B'.map B'.source B'.sink n where
  darts := P.darts.map I.toEquiv
  vertices := P.vertices.map I.vertexEquiv
  darts_length := by simp [P.darts_length]
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map I.vertexEquiv.injective
  start_vertex := by
    simpa using (congrArg I.vertexEquiv P.start_vertex).trans I.vertexEquiv_source
  end_vertex := by
    simpa using (congrArg I.vertexEquiv P.end_vertex).trans I.vertexEquiv_sink
  edge_step := by
    intro i
    have hiMap := i.isLt
    simp only [List.length_map] at hiMap
    have hi : i.val < n := by simpa [P.darts_length] using hiMap
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
    let jv : Fin P.vertices.length := ⟨i.val, by
      rw [P.vertices_length]
      omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by
      rw [P.vertices_length]
      omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map I.toEquiv).get i = I.toEquiv (P.darts.get j) := by
      simp [j]
    have hgetV : (P.vertices.map I.vertexEquiv).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv) := by
      simp [jv]
    have hgetV' : (P.vertices.map I.vertexEquiv).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv') := by
      simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hm
      exact h.1 ((I.missing_iff _).mp hm)
    · exact (I.tail_iff _).2 h.2.1
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv) := hgetV
        _ = I.vertexEquiv (dartTailVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.1
        _ = dartTailVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartTailVertex _
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv') := hgetV'
        _ = I.vertexEquiv (dartHeadVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.2
        _ = dartHeadVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartHeadVertex _

/-- The longest source-to-sink path length is invariant under an
orientation-preserving boundary isomorphism (`lem-lr-ind`, -/
theorem ldpLengthBase_eq_of_baseIso
    {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') : ldpLengthBase B' = ldpLengthBase B := by
  apply Nat.le_antisymm
  · obtain ⟨P, _⟩ := (mem_sourceSinkPathLengthsBase B'
      (ldpLengthBase B')).mp (ldpLengthBase_mem B')
    exact le_ldpLengthBase B (I.symm.transportPath P)
  · obtain ⟨P, _⟩ := (mem_sourceSinkPathLengthsBase B
      (ldpLengthBase B)).mp (ldpLengthBase_mem B)
    exact le_ldpLengthBase B' (I.transportPath P)

/-- The shortest source-to-sink path length is invariant under an
orientation-preserving boundary isomorphism (`lem-lr-ind`, -/
theorem sdpLengthBase_eq_of_baseIso
    {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') : sdpLengthBase B' = sdpLengthBase B := by
  apply Nat.le_antisymm
  · obtain ⟨P, _⟩ := (mem_sourceSinkPathLengthsBase B
      (sdpLengthBase B)).mp (sdpLengthBase_mem B)
    exact sdpLengthBase_le B' (I.transportPath P)
  · obtain ⟨P, _⟩ := (mem_sourceSinkPathLengthsBase B'
      (sdpLengthBase B')).mp (sdpLengthBase_mem B')
    exact sdpLengthBase_le B (I.symm.transportPath P)

/-- The selected extremal source-to-sink path length on a helper isomorphism
class. Invariance under boundary isomorphism makes this well-defined; helper
toward `lem-lr-ind` / `def-boltzmann-lr`
and this is not the paper result. -/
@[expose] noncomputable def xdpLenClass {ℓ r n : ℕ} (x : XDP) :
    KMSWMapIsoClass ℓ r n → ℕ :=
  KMSWMapIsoClass.lift
    (fun R : KMSWMapRep ℓ r n => xdpLengthBase R.B x)
    (by
      intro R R' h
      rcases h with ⟨I⟩
      cases x with
      | ldp => exact (ldpLengthBase_eq_of_baseIso I).symm
      | sdp => exact (sdpLengthBase_eq_of_baseIso I).symm)

/-- On a quotient class represented by `R`, `xdpLenClass` equals the base
length of `R`. Helper toward `lem-lr-ind` / `def-boltzmann-lr`
and this is not the paper result. -/
theorem xdpLenClass_mk {ℓ r n : ℕ} (x : XDP) (R : KMSWMapRep ℓ r n) :
    xdpLenClass x (KMSWMapIsoClass.mk R) = xdpLengthBase R.B x := by
  rfl

/-- The selected extremal path length on an unrooted map in the Boltzmann
space. Helper toward `lem-lr-ind` / `def-boltzmann-lr`
and this is not the paper result. -/
@[expose] noncomputable def xdpLen {ℓ r : ℕ} (x : XDP)
    (ω : BoltzmannSpace ℓ r) : ℕ := xdpLenClass x ω.2

/-- Maps whose selected extremal path length is `s`. Helper toward
normalizer finiteness is not assumed, and this is not the paper result. -/
@[expose] def boltzmannFiber {ℓ r : ℕ} (x : XDP) (s : ℕ) :
    Set (BoltzmannSpace ℓ r) := {ω | xdpLen x ω = s}

/-- The mass of a selected-length fiber is its unnormalized Boltzmann weight
divided by the partition function. This helper toward `lem-lr-ind` /
normalizer hypotheses, does not assume finiteness, and is not the paper
result. -/
theorem boltzmannLaw_fiber {ℓ r : ℕ}
    (h0 : boltzmannPartition ℓ r ≠ 0)
    (htop : boltzmannPartition ℓ r ≠ ⊤) (x : XDP) (s : ℕ) :
    boltzmannLaw ℓ r h0 htop (boltzmannFiber (ℓ := ℓ) (r := r) x s) =
      (∑' ω : boltzmannFiber (ℓ := ℓ) (r := r) x s,
        boltzmannWeight (ℓ := ℓ) (r := r) ω.1) /
        boltzmannPartition ℓ r := by
  classical
  have htsum :
      (∑' ω : BoltzmannSpace ℓ r,
        boltzmannWeight (ℓ := ℓ) (r := r) ω *
          (boltzmannFiber (ℓ := ℓ) (r := r) x s).indicator 1 ω) =
        ∑' ω : boltzmannFiber (ℓ := ℓ) (r := r) x s,
          boltzmannWeight (ℓ := ℓ) (r := r) ω.1 := by
    rw [tsum_subtype (boltzmannFiber (ℓ := ℓ) (r := r) x s)
      (boltzmannWeight (ℓ := ℓ) (r := r))]
    apply tsum_congr
    intro ω
    simp [Set.indicator_apply, mul_comm]
  have hmass :
      Measure.sum
          (fun ω : BoltzmannSpace ℓ r =>
            boltzmannWeight ω • Measure.dirac ω)
          (boltzmannFiber (ℓ := ℓ) (r := r) x s) =
        ∑' ω : BoltzmannSpace ℓ r,
          boltzmannWeight ω *
            (boltzmannFiber (ℓ := ℓ) (r := r) x s).indicator 1 ω := by
    rw [Measure.sum_apply _ (by simp [boltzmannFiber])]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
      Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
  rw [boltzmannLaw, Measure.smul_apply, smul_eq_mul, hmass, htsum,
    div_eq_mul_inv]
  rw [mul_comm]

/-- The selected-length fibers partition the normalized Boltzmann law. This
helper toward `lem-lr-ind` / `def-boltzmann-lr`
does not assume finiteness, and is not the paper result. -/
theorem boltzmannLaw_fiber_sum_eq_one {ℓ r : ℕ}
    (h0 : boltzmannPartition ℓ r ≠ 0)
    (htop : boltzmannPartition ℓ r ≠ ⊤) (x : XDP) :
    ∑' s : ℕ,
      boltzmannLaw ℓ r h0 htop (boltzmannFiber (ℓ := ℓ) (r := r) x s) = 1 := by
  have hfiber (s : ℕ) :
      (fun ω : BoltzmannSpace ℓ r => xdpLen x ω) ⁻¹' ({s} : Set ℕ) =
        boltzmannFiber (ℓ := ℓ) (r := r) x s := by
    ext ω
    simp [boltzmannFiber]
  have hdecomp :
      ∑' s : ℕ,
        ∑' ω : boltzmannFiber (ℓ := ℓ) (r := r) x s,
          boltzmannWeight (ℓ := ℓ) (r := r) ω.1 =
        boltzmannPartition ℓ r := by
    calc
      ∑' s : ℕ,
          ∑' ω : boltzmannFiber (ℓ := ℓ) (r := r) x s,
            boltzmannWeight (ℓ := ℓ) (r := r) ω.1 =
          ∑' s : ℕ,
            ∑' ω :
                (fun ω : BoltzmannSpace ℓ r => xdpLen x ω) ⁻¹' ({s} : Set ℕ),
              boltzmannWeight (ℓ := ℓ) (r := r) ω.1 := by
        apply tsum_congr
        intro s
        rw [← hfiber s]
      _ = boltzmannPartition ℓ r := by
        simpa [boltzmannPartition] using
          (tsum_fiberwise
        (f := fun ω : BoltzmannSpace ℓ r => boltzmannWeight ω)
        (g := fun ω : BoltzmannSpace ℓ r => xdpLen x ω))
  calc
    ∑' s : ℕ,
        boltzmannLaw ℓ r h0 htop (boltzmannFiber (ℓ := ℓ) (r := r) x s) =
        ∑' s : ℕ,
          (∑' ω : boltzmannFiber (ℓ := ℓ) (r := r) x s,
            boltzmannWeight (ℓ := ℓ) (r := r) ω.1) /
              boltzmannPartition ℓ r := by
      apply tsum_congr
      intro s
      exact boltzmannLaw_fiber h0 htop x s
    _ = (∑' s : ℕ,
          ∑' ω : boltzmannFiber (ℓ := ℓ) (r := r) x s,
            boltzmannWeight (ℓ := ℓ) (r := r) ω.1) *
          (boltzmannPartition ℓ r)⁻¹ := by
      simp_rw [div_eq_mul_inv]
      exact ENNReal.tsum_mul_right
    _ = boltzmannPartition ℓ r * (boltzmannPartition ℓ r)⁻¹ := by
      rw [hdecomp]
    _ = 1 := by
      rw [mul_comm]
      exact ENNReal.inv_mul_cancel h0 htop

end DirectedDistances.PlanarMap
