module

public import DirectedDistances.KMSW.KMSWLeftUniformLaw
public import DirectedDistances.KMSW.KMSWLeftLLFirstHit
public import DirectedDistances.KMSW.KMSWLeftDirectRun

/-! # Finite disk samples and their first-hit exploration times

The carrier has `N = n + ℓ` total geometric edges and `n - 1` non-boundary
edges. The source parameter is `ℓ = ℓₙ + 1`. This is the Lemma 3.19 procedure
The normalized counting laws allow empty carriers, in which case they are zero.
No boundary-order transport through `DirectedMapWithMissingIso` is asserted. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap MeasureTheory



theorem kmswDiskFiniteSample_index_bound {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    (kmswStage u n).LL.length = ℓ - 1 ∧
      k.val + 1 ≤ (kmswStage u n).LL.length := by
  have hlen := (kmswLeftRun_admissible_lengths ℓ n c.val c.property).2.2.1
  exact ⟨hlen, by rw [hlen]; exact k.isLt⟩



@[expose] noncomputable def kmswDiskFirstHit {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) : ℕ :=
  Nat.find (kmswLL_level_hit (finiteCodeExtend (n := n + 1) c.val) n
    (k.val + 1) (by omega) (kmswDiskFiniteSample_index_bound c k).2)

private theorem disk_L_step (u : ℕ → Fin 3) (i : ℕ) :
    |L u (i + 1) - L u i| ≤ 1 := by
  have hs : L u (i + 1) = L u i + ((u i : ℤ) - 1) :=
    Finset.sum_range_succ _ _
  rw [hs]
  have hi := (u i).isLt
  apply abs_le.mpr
  constructor <;> omega

/-- end is the edge allocated at the first hit; the coordinate starts at zero. -/
theorem kmswDiskFirstHit_spec {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    0 < T ∧ T ≤ n ∧ L u 0 = 0 ∧ L u T = -((k.val + 1 : ℕ) : ℤ) ∧
      (∀ j < T, L u j > -((k.val + 1 : ℕ) : ℤ)) ∧
      (kmswStage u n).LL.reverse.get
        ⟨k.val, by simpa only [List.length_reverse] using
          (show k.val < (kmswStage u n).LL.length from
            (kmswDiskFiniteSample_index_bound c k).2)⟩ =
        kmswLLCreatedEdge u T := by
  let u := finiteCodeExtend (n := n + 1) c.val
  have hk : 1 ≤ k.val + 1 := by omega
  have hkn := (kmswDiskFiniteSample_index_bound c k).2
  let hhit := kmswLL_level_hit u n (k.val + 1) hk hkn
  have he := kmswLL_reverse_get_first_hit u n (k.val + 1) hk hkn
  have hzero : L u 0 = 0 := by simp only [L, Finset.range_zero, Finset.sum_empty]
  have hrec := (strict_running_minimum_iff_first_hit (L u) hzero
    (disk_L_step u) (Nat.find hhit) (Nat.find hhit)
    (-((k.val + 1 : ℕ) : ℤ)) (by omega) hhit).mpr
      ⟨le_rfl, Nat.find_spec hhit, rfl⟩
  have hbefore := (Finset.mem_filter.mp hrec.1).2
  refine ⟨he.1, he.2.1, hzero, Nat.find_spec hhit, ?_, ?_⟩
  · intro j hj
    have h := hbefore j hj
    rw [Nat.find_spec hhit] at h
    exact h
  · exact he.2.2

/-- selected edge by stage `n` is the fresh-left triangle of step `T - 1`. -/
theorem kmswDiskFirstHit_triangle {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    ∃ j : TriangleCreationTime u,
      j.val = T - 1 ∧ j.val < n ∧ u j.val = 0 ∧
      (kmswStage u j.val).UL.dropLast = [] ∧
      stageTriangleDartTriple u j =
        (((kmswStage u j.val).active, false),
         ((kmswStage u j.val).nextEdge, true), (kmswLLCreatedEdge u T, false)) ∧
      (kmswLLCreatedEdge u T, false) ∈ stageTriangleDartList u j ∧
      (kmswStage u T).present (kmswLLCreatedEdge u T) = false ∧
      (∀ (r : ℕ) (hjr : j.val < r),
        FaceSucc3Cycle (kmswMap u r).faceSucc
          (stageTriangleDart₁ u r j hjr) (stageTriangleDart₂ u r j hjr)
          (stageTriangleDart₃ u r j hjr)) ∧
      ∀ i : TriangleCreationTime u,
        (i.val < n ∧ ∃ b : Bool,
          (kmswLLCreatedEdge u T, b) ∈ stageTriangleDartList u i) → i = j := by
  let u := finiteCodeExtend (n := n + 1) c.val
  have hk : 1 ≤ k.val + 1 := by omega
  have hkn := (kmswDiskFiniteSample_index_bound c k).2
  obtain ⟨j, hjT, hjn, hjcode, hjdrop, hjtriple, hjmem, hjmissing, hjface⟩ :=
    kmswLL_first_hit_triangle u n (k.val + 1) hk hkn
  obtain ⟨j₀, _, huniq⟩ := kmswLL_first_hit_unique_triangle u n (k.val + 1) hk hkn
  refine ⟨j, hjT, hjn, hjcode, hjdrop, hjtriple, hjmem, hjmissing, hjface, ?_⟩
  intro i hi
  exact (huniq i hi).trans (huniq j ⟨hjn, false, hjmem⟩).symm

/-- walk/index law; the source index is `K = k.val + 1`. -/
theorem kmswDiskFiniteSample_uniform_prod (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    ((uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map
        (fun p => ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1, p.2)) =
      (uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
        (uniformCountingMeasure (Fin (ℓ - 1))) :=
  kmswLeftEndpointSideEquiv_symm_uniform_prod ℓ n hℓ

/-- time) has the pushforward law obtained from an independent uniform walk/index. -/
theorem kmswDiskFiniteSample_uniform_firstHit (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace ℕ := ⊤
    ((uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map
        (fun p => let c := (kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1
          (c, kmswDiskFirstHit c p.2)) =
      ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
        (uniformCountingMeasure (Fin (ℓ - 1)))).map
        (fun p => (p.1, kmswDiskFirstHit p.1 p.2)) := by
  let : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n) (kmswLeftEndpointSideEquiv ℓ n hℓ)
  let : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  let : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  let : MeasurableSpace ℕ := ⊤
  let f := fun p : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} × Fin (ℓ - 1) =>
    ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm p.1, p.2)
  let g := fun p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1) =>
    (p.1, kmswDiskFirstHit p.1 p.2)
  have hf : Measurable f := measurable_of_countable f
  have hg : Measurable g := measurable_of_countable g
  have h := congrArg (fun μ => μ.map g) (kmswDiskFiniteSample_uniform_prod ℓ n hℓ)
  rw [Measure.map_map hg hf] at h
  exact h

/-- the encoded direct stage map. `kmswDiskFirstHit_spec` and
`kmswDiskFirstHit_triangle` identify the selected edge within that stage map.
Transport of the boundary order through this isomorphism is not claimed. -/
theorem kmswDiskFiniteSample_partialMapIso (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}) :
    Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
      (kmswStageDirectedMap
        (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv ℓ n hℓ).symm q).val) n)) :=
  (kmswLeftEndpointSideEquiv_symm_uniform_partialMapIso ℓ n hℓ).2 q

end DirectedDistances.KMSW
