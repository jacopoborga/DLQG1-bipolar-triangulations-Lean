module

public import DirectedDistances.KMSW.WindowCodeDecoder
public import DirectedDistances.KMSW.KMSWWholePlaneBallCapture

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The centre remains parametric, and no root frame is chosen. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem disk_window_valid {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
  unfold bridgeOptionWindow at h
  split at h
  · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
  · contradiction

private theorem disk_window_code {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    ∀ i < 2 * N,
      (fun j => p.1 (j + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + i) =
        windowCodeDecode N x i := by
  intro i hi
  exact (windowCodeDecode_bridge h i hi).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
The identity holds at every stage after the valid window ends. -/
theorem kmswDiskBallVertices_eq_image_future {n N r c : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEvent (windowCodeDecode N x) (2 * N) r c)
    (n' : ℕ) (hn' : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n') :
    kmswStageBallVertices (fun _ _ => True) (kmswStage (fun i => p.1 (i + 1)) n') r
        (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N) c) =
      (kmswStageBallVertices (fun _ _ => True)
        (kmswStage (windowCodeDecode N x) (2 * N)) r c).image
          (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
            ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)) := by
  have hNT := (disk_window_valid h).1
  exact (kmswWindowCaptureEvent_ballVerticesImageEq_future
    (windowCodeDecode N x) (2 * N) r c hev (fun i => p.1 (i + 1))
    ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (disk_window_code h)
    n' (by omega)).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Specialization to the full bridge stage, with no additional endpoint premise. -/
theorem kmswDiskBallVertices_eq_image {n N r c : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEvent (windowCodeDecode N x) (2 * N) r c) :
    kmswStageBallVertices (fun _ _ => True) (kmswStage (fun i => p.1 (i + 1)) n) r
        (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
          ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N) c) =
      (kmswStageBallVertices (fun _ _ => True)
        (kmswStage (windowCodeDecode N x) (2 * N)) r c).image
          (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
            ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)) := by
  exact kmswDiskBallVertices_eq_image_future h hev n (disk_window_valid h).2

private theorem disk_window_fresh {n N r c : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEvent (windowCodeDecode N x) (2 * N) r c) :
    let w := fun i => p.1 (i + 1)
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    ∀ v ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage (windowCodeDecode N x) (2 * N)) r c,
      v < (kmswStage (fun i => w (s + i)) (2 * N)).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s (2 * N) v := by
  classical
  dsimp only
  intro v hv
  have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
  have hs := kmswStage_windowCodeDecode_bridge h (2 * N) le_rfl
  refine ⟨?_, kmswWindowPatchVertexMap_fresh_for_every_prefix
    (windowCodeDecode N x) (2 * N) v hb (hev.2.1 v hv).1 (hev.2.1 v hv).2
    (fun i => p.1 (i + 1))
    ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (disk_window_code h)⟩
  rw [← hs]
  exact hb

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
At the window endpoint, induced geometric edges correspond bijectively, retaining
edge identity and multiedges. The target vertex set is exactly the disk ball there. -/
theorem kmswDiskBallInducedEdgesBijective_at_window_end {n N r c : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEvent (windowCodeDecode N x) (2 * N) r c) :
    let w := fun i => p.1 (i + 1)
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    let S := kmswStageBallVertices (fun _ _ => True)
      (kmswStage (windowCodeDecode N x) (2 * N)) r c
    kmswStageBallVertices (fun _ _ => True) (kmswStage w (s + 2 * N)) r
        (kmswWindowPatchVertexMap w s (2 * N) c) =
      S.image (kmswWindowPatchVertexMap w s (2 * N)) ∧
    Function.Bijective (kmswWindowFreshSetEdgeMapOn w s (2 * N) S) := by
  dsimp only
  have hNT := (disk_window_valid h).1
  refine ⟨kmswDiskBallVertices_eq_image_future h hev _ (by omega), ?_⟩
  exact kmswWindowFreshSetEdgeMap_bijective _ _ _ _ (disk_window_fresh h hev)

private theorem equiv_of_common_image {α β γ : Type*}
    (S : Set α) (D : Set β) (C : Set γ) (f : α → β) (g : α → γ)
    (hf : Set.InjOn f S) (hg : Set.InjOn g S)
    (hD : D = f '' S) (hC : C = g '' S) :
    ∃ e : D ≃ C, ∀ (d : D) (v : α), v ∈ S → d.val = f v → (e d).val = g v := by
  classical
  let f' : S → D := fun v => ⟨f v.val, by
    rw [hD]
    exact ⟨v.val, v.property, rfl⟩⟩
  let g' : S → C := fun v => ⟨g v.val, by
    rw [hC]
    exact ⟨v.val, v.property, rfl⟩⟩
  have hf' : Function.Bijective f' := by
    constructor
    · intro a b hab
      exact Subtype.ext (hf a.property b.property (congrArg Subtype.val hab))
    · intro d
      have hd : d.val ∈ f '' S :=
        (congrArg (fun A : Set β => d.val ∈ A) hD).mp d.property
      obtain ⟨v, hv, hvd⟩ := hd
      exact ⟨⟨v, hv⟩, Subtype.ext hvd⟩
  have hg' : Function.Bijective g' := by
    constructor
    · intro a b hab
      exact Subtype.ext (hg a.property b.property (congrArg Subtype.val hab))
    · intro d
      have hd : d.val ∈ g '' S :=
        (congrArg (fun A : Set γ => d.val ∈ A) hC).mp d.property
      obtain ⟨v, hv, hvd⟩ := hd
      exact ⟨⟨v, hv⟩, Subtype.ext hvd⟩
  let ef := Equiv.ofBijective f' hf'
  let eg := Equiv.ofBijective g' hg'
  refine ⟨ef.symm.trans eg, ?_⟩
  intro d v hv hd
  have hdf : d = ef ⟨v, hv⟩ := Subtype.ext hd
  rw [hdf]
  change (eg (ef.symm (ef ⟨v, hv⟩))).val = g v
  rw [ef.symm_apply_apply]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Compatible disk and colimit balls are images of the same decoded window ball.
Their vertex bijection commutes with both window maps; the centre is parametric. -/
theorem kmswDiskWholePlaneBall_coupling {n N r c : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEvent (windowCodeDecode N x) (2 * N) r c)
    (W : ℤ → Fin 3)
    (hW : ∀ i < 2 * N, shiftedStream W N i = windowCodeDecode N x i)
    (n' : ℕ) (hn' : (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n') :
    let w := fun i => p.1 (i + 1)
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    let S := kmswStageBallVertices (fun _ _ => True)
      (kmswStage (windowCodeDecode N x) (2 * N)) r c
    let D := kmswStageBallVertices (fun _ _ => True) (kmswStage w n') r
      (kmswWindowPatchVertexMap w s (2 * N) c)
    let C := wholePlaneBallVertices W r (wholePlaneVertexι W N c)
    D = S.image (kmswWindowPatchVertexMap w s (2 * N)) ∧
      C = (wholePlaneVertexι W N) '' (S : Set ℕ) ∧
      ∃ e : {v // v ∈ D} ≃ {v // v ∈ C},
        ∀ (d : {v // v ∈ D}) (v : ℕ), v ∈ S →
          d.val = kmswWindowPatchVertexMap w s (2 * N) v →
          (e d).val = wholePlaneVertexι W N v := by
  classical
  dsimp only
  have hD := kmswDiskBallVertices_eq_image_future h hev n' hn'
  have hs : kmswStage (shiftedStream W N) (2 * N) =
      kmswStage (windowCodeDecode N x) (2 * N) := kmswStage_congr hW
  have heW : kmswWindowCaptureEvent (shiftedStream W N) (2 * N) r c :=
    (kmswWindowCaptureEvent_congr _ _ _ _ _ hW).mpr hev
  have hC := wholePlaneBallVertices_eq_image_of_windowCaptureEvent W N (2 * N) r c heW
  rw [hs] at hC
  refine ⟨hD, hC, ?_⟩
  apply equiv_of_common_image
    (↑(kmswStageBallVertices (fun _ _ => True)
      (kmswStage (windowCodeDecode N x) (2 * N)) r c) : Set ℕ)
    (↑(kmswStageBallVertices (fun _ _ => True) (kmswStage (fun i => p.1 (i + 1)) n') r
      (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
        ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N) c)) : Set ℕ)
    (wholePlaneBallVertices W r (wholePlaneVertexι W N c))
    (kmswWindowPatchVertexMap (fun i => p.1 (i + 1))
      ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)) (wholePlaneVertexι W N)
  · intro a ha b hb hab
    exact kmswWindowPatchVertexMap_injOn _ _ _
      (disk_window_fresh h hev a ha).1 (disk_window_fresh h hev b hb).1 hab
  · intro a _ b _ hab
    exact wholePlaneVertexι_injective W N hab
  · ext v
    rw [hD]
    exact Finset.mem_image
  · exact hC

end DirectedDistances.KMSW
