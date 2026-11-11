module

public import DirectedDistances.KMSW.KMSWLeftProcedurePartial
public import DirectedDistances.PlanarMap.BdyReverseBijective
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Uniform law transport for the left KMSW procedure reading

These helpers do not certify Proposition 5.16 or the printed Lemma 3.19.
The counting-normalized measures are zero when the equivalent carriers are empty.
The index `k : Fin (ℓ - 1)` represents the source index `k.val + 1` in `[1, ℓ - 1]`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap MeasureTheory

/-- uniform law transport through the Lemma 3.19 procedure-reading bijection
The forward law uses discrete sigma-algebras and permits empty carriers. -/
theorem kmswLeftEndpointSideEquiv_uniform (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    (uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).map
        (kmswLeftEndpointSideEquiv ℓ n hℓ) =
      uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  exact uniformCountingMeasure_map_of_bijective _
    (kmswLeftEndpointSideEquiv ℓ n hℓ).bijective

/-- uniform law transport through the Lemma 3.19 procedure-reading bijection
A uniform class gives a uniform walk, also when both carriers are empty. -/
theorem kmswLeftEndpointSideEquiv_symm_uniform (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    (uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).map
        (kmswLeftEndpointSideEquiv ℓ n hℓ).symm =
      uniformCountingMeasure (KMSWLeftWalkClass ℓ n) := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  exact uniformCountingMeasure_map_of_bijective _
    (kmswLeftEndpointSideEquiv ℓ n hℓ).symm.bijective

/-- uniform law transport through the Lemma 3.19 procedure-reading bijection
The independent uniform index is retained; `k.val + 1` is the source index. -/
theorem kmswLeftEndpointSideEquiv_symm_uniform_prod (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    ((uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map
        (fun p => ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1, p.2)) =
      (uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
        (uniformCountingMeasure (Fin (ℓ - 1))) := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  let : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  have : SFinite (uniformCountingMeasure (Fin (ℓ - 1))) := by
    unfold uniformCountingMeasure
    infer_instance
  have hm := Measure.map_prod_map
    (uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled})
    (uniformCountingMeasure (Fin (ℓ - 1)))
    (measurable_of_countable (kmswLeftEndpointSideEquiv ℓ n hℓ).symm) measurable_id
  simpa only [kmswLeftEndpointSideEquiv_symm_uniform ℓ n hℓ, Measure.map_id,
    Prod.map_def, id_eq] using hm.symm

/-- uniform law transport through the Lemma 3.19 procedure-reading bijection
The transported uniform walk encodes the decorated partial map of each sample. -/
theorem kmswLeftEndpointSideEquiv_symm_uniform_partialMapIso
    (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    (uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).map
        (kmswLeftEndpointSideEquiv ℓ n hℓ).symm =
      uniformCountingMeasure (KMSWLeftWalkClass ℓ n) ∧
    ∀ q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled},
      Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
        (kmswStageDirectedMap
          (finiteCodeExtend (n := n + 1)
            ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm q).val) n)) := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  refine ⟨kmswLeftEndpointSideEquiv_symm_uniform ℓ n hℓ, ?_⟩
  intro q
  have h := kmswLeftEndpointSideEquiv_partialMapIso ℓ n hℓ
    ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm q)
  have hq := (kmswLeftEndpointSideEquiv ℓ n hℓ).apply_symm_apply q
  rw [hq] at h
  exact h

end DirectedDistances.KMSW
