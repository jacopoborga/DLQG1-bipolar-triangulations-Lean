/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWProcedureReading
public import DirectedDistances.PlanarMap.BipolarInverseWalkCharacterization
public import DirectedDistances.PlanarMap.BdyReverseBijective
public import Mathlib.Probability.Independence.Basic

/-! Supporting lemmas for paper labels `prop-kmsw-uibot` (see CORRESPONDENCE.md). -/

/- # The finite uniformly edge-rooted sample for Proposition 3.9

uniform isomorphism class with fixed positive left and right boundary lengths
and exactly `n` edges, then independently chooses one of all `n` edges.
Enumeration is transported from the actual finite walk class by the unconditional
procedure-reading equivalence. Nonemptiness is required, rather than an

These are finite-law producers only. They do not prove Proposition 3.9,
construct its positive-radius local topology observables, or assert convergence. The
procedure-reading source qualification of the imported KMSW equivalence is -/

public section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped ENNReal

/-- Finite enumeration of the actual map isomorphism classes, transported from
finite admissible KMSW words. Helper for `prop-kmsw-uibot` -/
@[expose, instance_reducible] noncomputable def uibotFiniteMapFintype (ℓ ρ n : ℕ) (hn : 1 ≤ n) :
    Fintype (KMSWMapIsoClass ℓ ρ n) :=
  Fintype.ofEquiv (KMSWWalkClass ℓ ρ n) (kmswProcedureEquiv ℓ ρ n hn)



theorem uibotFiniteMapFintype_card (ℓ ρ n : ℕ) (hn : 1 ≤ n) :
    letI := uibotFiniteMapFintype ℓ ρ n hn
    Fintype.card (KMSWMapIsoClass ℓ ρ n) = Fintype.card (KMSWWalkClass ℓ ρ n) := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  exact Fintype.card_congr (kmswProcedureEquiv ℓ ρ n hn).symm

private theorem uniformCountingMeasure_probability (α : Type*) [Fintype α]
    [MeasurableSpace α] [Nonempty α] :
    IsProbabilityMeasure (uniformCountingMeasure α) := by
  constructor
  change (Fintype.card α : ℝ≥0∞)⁻¹ * Measure.count Set.univ = 1
  have hc : (Measure.count : Measure α) Set.univ = (Fintype.card α : ℝ≥0∞) := by
    simpa only [Finset.coe_univ, Finset.card_univ] using
      (Measure.count_apply_finset' (α := α) (s := Finset.univ) (by simp))
  rw [hc]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)

/-- The actual finite sampling law for `prop-kmsw-uibot`
independent uniform index among ALL `n` edges, with fixed positive boundary
lengths. The carrier must actually be nonempty. -/
@[expose] noncomputable def uibotFiniteUniformSampleLaw
    (ℓ ρ n : ℕ) (_hℓ : 0 < ℓ) (_hρ : 0 < ρ) (hn : 1 ≤ n)
    (_hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    letI : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
    letI : MeasurableSpace (Fin n) := ⊤
    Measure (KMSWMapIsoClass ℓ ρ n × Fin n) := by
  letI := uibotFiniteMapFintype ℓ ρ n hn
  letI : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
  letI : MeasurableSpace (Fin n) := ⊤
  exact (uniformCountingMeasure (KMSWMapIsoClass ℓ ρ n)).prod
    (uniformCountingMeasure (Fin n))

section FiniteLaw

variable (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
  (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))

local instance : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
local instance : MeasurableSpace (Fin n) := ⊤

/-- Exact source product formula, on the actual unlabelled map carrier. -/
theorem uibotFiniteUniformSampleLaw_eq :
    letI := uibotFiniteMapFintype ℓ ρ n hn
    uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne =
      (uniformCountingMeasure (KMSWMapIsoClass ℓ ρ n)).prod
        (uniformCountingMeasure (Fin n)) := rfl

/-- Normalization of the actual finite map-and-edge-index law. Helper for -/
theorem uibotFiniteUniformSampleLaw_probability :
    IsProbabilityMeasure (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne) := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  let := hne
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let := uniformCountingMeasure_probability (KMSWMapIsoClass ℓ ρ n)
  let := uniformCountingMeasure_probability (Fin n)
  rw [uibotFiniteUniformSampleLaw_eq]
  infer_instance

/-- The map marginal is uniform on isomorphism classes, with no weighting
by labelled representatives or automorphism orbits. Helper for -/
theorem uibotFiniteUniformSampleLaw_map_fst :
    letI := uibotFiniteMapFintype ℓ ρ n hn
    (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne).map Prod.fst =
      uniformCountingMeasure (KMSWMapIsoClass ℓ ρ n) := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let := uniformCountingMeasure_probability (Fin n)
  rw [uibotFiniteUniformSampleLaw_eq, Measure.map_fst_prod, measure_univ, one_smul]

/-- The independent root index has the uniform law on all `n` indices. -/
theorem uibotFiniteUniformSampleLaw_map_snd :
    (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne).map Prod.snd =
      uniformCountingMeasure (Fin n) := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  let := hne
  let := uniformCountingMeasure_probability (KMSWMapIsoClass ℓ ρ n)
  rw [uibotFiniteUniformSampleLaw_eq, Measure.map_snd_prod, measure_univ, one_smul]

/-- Independence under the actual product law, rather than a premise of a -/
theorem uibotFiniteUniformSampleLaw_indepFun :
    IndepFun Prod.fst Prod.snd (uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne) := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  let := hne
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let := uniformCountingMeasure_probability (KMSWMapIsoClass ℓ ρ n)
  let := uniformCountingMeasure_probability (Fin n)
  rw [uibotFiniteUniformSampleLaw_eq]
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

end FiniteLaw

section PeanoRooting

variable {ℓ ρ n : ℕ}

/-- The Peano index names an actual geometric edge orbit, not an adjacency
pair, so parallel edges remain distinct. Helper for `prop-kmsw-uibot` -/
@[expose] noncomputable def uibotPeanoEdgeEquiv (R : KMSWMapRep ℓ ρ n) :
    Fin n ≃ CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap :=
  (finCongr R.edges.symm).trans
    (Equiv.ofBijective _ (peanoEdge_bijective_edges R.B))



@[expose, instance_reducible] noncomputable def uibotFiniteEdgeFintype
    (R : KMSWMapRep ℓ ρ n) :
    Fintype (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) :=
  Fintype.ofEquiv (Fin n) (uibotPeanoEdgeEquiv R)

/-- Every geometric edge, including every boundary edge, occurs exactly once. -/
theorem uibotPeanoEdgeEquiv_apply (R : KMSWMapRep ℓ ρ n) (j : Fin n) :
    uibotPeanoEdgeEquiv R j =
      Quotient.mk (Equiv.Perm.SameCycle.setoid R.B.map.toCombinatorialMap.edgeInv)
        (peanoEdge R.B (Fin.cast R.edges.symm j)) := rfl

/-- The actual inverse Peano index recovers the selected index. Helper for -/
theorem uibotPeanoEdge_index (R : KMSWMapRep ℓ ρ n) (j : Fin n) :
    Fin.cast R.edges (peanoIndex R.B (peanoEdge R.B (Fin.cast R.edges.symm j))) = j := by
  rw [peanoIndex_peanoEdge]
  rfl

/-- A uniform Peano index transports to uniform counting measure on ALL
actual geometric edges of each fixed representative. Helper for -/
theorem uibotPeanoEdgeEquiv_uniform (R : KMSWMapRep ℓ ρ n) :
    letI := uibotFiniteEdgeFintype R
    letI : MeasurableSpace (Fin n) := ⊤
    letI : MeasurableSpace
      (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) := ⊤
    (uniformCountingMeasure (Fin n)).map (uibotPeanoEdgeEquiv R) =
      uniformCountingMeasure
        (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) := by
  let := uibotFiniteEdgeFintype R
  let : MeasurableSpace (Fin n) := ⊤
  let : MeasurableSpace
    (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) := ⊤
  exact uniformCountingMeasure_map_of_bijective _ (uibotPeanoEdgeEquiv R).bijective

/-- Root the actual plane map at its indexed forward Peano dart. Helper for -/
@[expose] noncomputable def uibotPeanoRootedAt (R : KMSWMapRep ℓ ρ n) (j : Fin n) :
    RootedDirectedMapWithMissing (Fin R.dartCount) :=
  baseRootedAt R.B (peanoEdge R.B (Fin.cast R.edges.symm j))
    (peanoEdge_forward R.B (Fin.cast R.edges.symm j))

/-- The source geometric-edge rooting expressed without a choice of dart:
use the uniquely indexed forward dart of that edge. Helper for -/
@[expose] noncomputable def uibotGeometricEdgeRootedAt (R : KMSWMapRep ℓ ρ n)
    (e : CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) :
    RootedDirectedMapWithMissing (Fin R.dartCount) :=
  uibotPeanoRootedAt R ((uibotPeanoEdgeEquiv R).symm e)

/-- The selected root's geometric edge is precisely the supplied edge; no
boundary restriction or quotient by automorphism orbits is imposed. Helper -/
theorem uibotGeometricEdgeRootedAt_root (R : KMSWMapRep ℓ ρ n)
    (e : CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid R.B.map.toCombinatorialMap.edgeInv)
      (uibotGeometricEdgeRootedAt R e).root = e := by
  exact (uibotPeanoEdgeEquiv R).apply_symm_apply e

/-- Rooting at the independent uniform Peano index is uniform-edge rooting
conditional on the sampled representative. Helper for `prop-kmsw-uibot` -/
theorem uibotPeanoRootedAt_uniform (R : KMSWMapRep ℓ ρ n) :
    letI := uibotFiniteEdgeFintype R
    letI : MeasurableSpace (Fin n) := ⊤
    letI : MeasurableSpace
      (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) := ⊤
    letI : MeasurableSpace (RootedDirectedMapWithMissing (Fin R.dartCount)) := ⊤
    (uniformCountingMeasure (Fin n)).map (uibotPeanoRootedAt R) =
      (uniformCountingMeasure
        (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap)).map
          (uibotGeometricEdgeRootedAt R) := by
  let := uibotFiniteEdgeFintype R
  let : MeasurableSpace (Fin n) := ⊤
  let : MeasurableSpace
    (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) := ⊤
  let : MeasurableSpace (RootedDirectedMapWithMissing (Fin R.dartCount)) := ⊤
  rw [← uibotPeanoEdgeEquiv_uniform R,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext j
  exact congrArg (uibotPeanoRootedAt R) ((uibotPeanoEdgeEquiv R).symm_apply_apply j).symm

/-- Boundary/plane isomorphisms preserve rooting at each SAME Peano index.
Thus changing a representative introduces no automorphism multiplicity.
This preserves rotation, edge identity, direction, exterior face and root; -/
@[expose] noncomputable def uibotPeanoRootedAt_iso
    {R R' : KMSWMapRep ℓ ρ n} (I : BipolarBoundaryBaseIso R.B R'.B) (j : Fin n) :
    RootedDirectedMapIso (uibotPeanoRootedAt R j) (uibotPeanoRootedAt R' j) where
  dartEquiv := I.toEquiv
  rot_comm := I.rot_comm
  edgeFlip_comm := I.edgeInv_comm
  missing_iff := fun d => (I.missing_iff d).symm
  present_iff := fun d => not_congr (I.missing_iff d).symm
  tail_iff := fun d => (I.tail_iff d).symm
  outer_iff := fun d => (I.outer_iff d).symm
  root_comm := by
    have hj : Fin.cast I.numEdges_eq (Fin.cast R.edges.symm j) =
        Fin.cast R'.edges.symm j := Fin.ext rfl
    exact (hj ▸ inverseIso_peanoEdge I (Fin.cast R.edges.symm j)).symm

end PeanoRooting

section ConditionalRooting

variable (ℓ ρ n : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
  (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))

local instance : MeasurableSpace (KMSWMapIsoClass ℓ ρ n) := ⊤
local instance : MeasurableSpace (Fin n) := ⊤

/-- Each map-and-index pair has the same mass, the reciprocal number of map
classes times `1/n`. This samples isomorphism classes first and does not
weight maps by numbers of labelled representatives. Helper for -/
theorem uibotFiniteUniformSampleLaw_pair_mass
    (q : KMSWMapIsoClass ℓ ρ n) (j : Fin n) :
    uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne ({q} ×ˢ {j}) =
      (Nat.card (KMSWMapIsoClass ℓ ρ n) : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)⁻¹ := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let := uniformCountingMeasure_probability (Fin n)
  rw [uibotFiniteUniformSampleLaw_eq, Measure.prod_prod]
  simp only [uniformCountingMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_singleton, mul_one, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Every map class has exactly the same positive conditioning mass. -/
theorem uibotFiniteUniformSampleLaw_map_mass (q : KMSWMapIsoClass ℓ ρ n) :
    uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne ({q} ×ˢ Set.univ) =
      (Nat.card (KMSWMapIsoClass ℓ ρ n) : ℝ≥0∞)⁻¹ := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let := uniformCountingMeasure_probability (Fin n)
  rw [uibotFiniteUniformSampleLaw_eq, Measure.prod_prod, measure_univ, mul_one]
  simp only [uniformCountingMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.count_singleton, mul_one, Nat.card_eq_fintype_card]

/-- Conditioning on any map class is legitimate: its mass is nonzero. -/
theorem uibotFiniteUniformSampleLaw_map_mass_ne_zero
    (q : KMSWMapIsoClass ℓ ρ n) :
    uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne ({q} ×ˢ Set.univ) ≠ 0 := by
  rw [uibotFiniteUniformSampleLaw_map_mass]
  exact ENNReal.inv_ne_zero.mpr (by finiteness)

/-- The event-factorization characterization of conditional uniform rooting:
for EVERY representative of the sampled class, the root is uniform over all
its geometric edges. Together with the positive map mass and the rooted
isomorphism theorem above, this introduces no representative/automorphism -/
theorem uibotFiniteUniformSampleLaw_conditional_edge
    (R : KMSWMapRep ℓ ρ n)
    (E : Set (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap)) :
    letI := uibotFiniteEdgeFintype R
    letI : MeasurableSpace
      (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) := ⊤
    uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne
        ({KMSWMapIsoClass.mk R} ×ˢ (uibotPeanoEdgeEquiv R ⁻¹' E)) =
      uibotFiniteUniformSampleLaw ℓ ρ n hℓ hρ hn hne
        ({KMSWMapIsoClass.mk R} ×ˢ Set.univ) *
          uniformCountingMeasure
            (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) E := by
  let := uibotFiniteMapFintype ℓ ρ n hn
  let := uibotFiniteEdgeFintype R
  let : MeasurableSpace
    (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) := ⊤
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let := uniformCountingMeasure_probability (Fin n)
  have he : uniformCountingMeasure (Fin n) (uibotPeanoEdgeEquiv R ⁻¹' E) =
      uniformCountingMeasure
        (CombinatorialMap.EdgeQuotient R.B.map.toCombinatorialMap) E := by
    rw [← uibotPeanoEdgeEquiv_uniform R]
    exact (Measure.map_apply (measurable_of_countable _)
      MeasurableSpace.measurableSet_top).symm
  rw [uibotFiniteUniformSampleLaw_eq, Measure.prod_prod, Measure.prod_prod,
    measure_univ, mul_one, he]

end ConditionalRooting

end DirectedDistances.PaperProofs.Section3
