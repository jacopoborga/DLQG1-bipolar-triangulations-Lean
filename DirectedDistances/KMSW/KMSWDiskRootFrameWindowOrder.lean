module

public import DirectedDistances.KMSW.KMSWWindowDiskRootFrame
public import DirectedDistances.KMSW.KMSWDiskRootCenter

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
transported to the KMSW window; not the paper result. -/
theorem kmswDiskRootFrame_window_ordered {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1))
    (s : ℕ) (hs : s < kmswDiskFirstHit c k) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let m := n - s
    let v := fun i => u (s + i)
    ∃ d : StageDart (kmswStage v m).nextEdge,
      (kmswWindowPatchData u s m).φ d.1.val = kmswLLCreatedEdge u T ∧
      kmswWindowPatchVertexMap u s m
        (stageEndpoint (kmswStage v m) (edgeFlip _ d)) = activeInitial u T ∧
      kmswWindowPatchVertexMap u s m
        (stageEndpoint (kmswStage v m) d) = activeInitial u (T - 1) := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  let m := n - s
  let v := fun i => u (s + i)
  obtain ⟨hsm, d, he, _, hv, hb, hc⟩ := kmswDiskRootFrame_in_window c k s hs
  change s + m = n at hsm
  change (kmswWindowDartMap u s m d).1.val = (kmswDiskRootDart c k).1.val at hv
  change (kmswWindowDartMap u s m d).2 = (kmswDiskRootDart c k).2 at hb
  have hf := (kmswDiskRootDart_hit_frame_iff c k (kmswDiskRootDart c k)).mpr rfl
  have hhead := hc false
  have htail := hc true
  simp only [Bool.false_eq_true, ↓reduceIte] at hhead
  simp only [↓reduceIte] at htail
  have hhead' : stageEndpoint (kmswStage u n)
      (edgeFlip _ (kmswDiskRootDart c k)) =
      kmswWindowPatchVertexMap u s m
        (stageEndpoint (kmswStage v m) (edgeFlip _ d)) := by
    change (if !(kmswWindowDartMap u s m d).2 then
      (kmswStage u (s + m)).east (kmswWindowDartMap u s m d).1.val
      else (kmswStage u (s + m)).west (kmswWindowDartMap u s m d).1.val) =
        kmswWindowPatchVertexMap u s m
          (if !d.2 then (kmswStage v m).east d.1.val
           else (kmswStage v m).west d.1.val) at hhead
    change (if !(kmswDiskRootDart c k).2 then
      (kmswStage u n).east (kmswDiskRootDart c k).1.val
      else (kmswStage u n).west (kmswDiskRootDart c k).1.val) =
        kmswWindowPatchVertexMap u s m
          (if !d.2 then (kmswStage v m).east d.1.val
           else (kmswStage v m).west d.1.val)
    simpa only [hsm, hv, hb] using hhead
  have htail' : stageEndpoint (kmswStage u n) (kmswDiskRootDart c k) =
      kmswWindowPatchVertexMap u s m (stageEndpoint (kmswStage v m) d) := by
    change stageEndpoint (kmswStage u (s + m)) (kmswWindowDartMap u s m d) =
      kmswWindowPatchVertexMap u s m (stageEndpoint (kmswStage v m) d) at htail
    simpa only [stageEndpoint, hsm, hv, hb] using htail
  exact ⟨d, he, hhead'.symm.trans hf.2.1, htail'.symm.trans hf.2.2⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
transported to the KMSW window; not the paper result. The Boolean side is a
consequence of the ordered geometric endpoints, not an orientation of the missing edge. -/
theorem kmswDiskRootFrame_window_ordered_side {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1))
    (s : ℕ) (hs : s < kmswDiskFirstHit c k) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let m := n - s
    let v := fun i => u (s + i)
    ∀ d : StageDart (kmswStage v m).nextEdge,
      (kmswWindowPatchData u s m).φ d.1.val = kmswLLCreatedEdge u T →
      kmswWindowPatchVertexMap u s m
        (stageEndpoint (kmswStage v m) (edgeFlip _ d)) = activeInitial u T →
      kmswWindowPatchVertexMap u s m
        (stageEndpoint (kmswStage v m) d) = activeInitial u (T - 1) →
      d.2 = true := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  let m := n - s
  let v := fun i => u (s + i)
  intro d he hhead htail
  have hTn : T ≤ n := (kmswDiskFirstHit_spec c k).2.1
  have hsT : s < T := hs
  have hsm : s + m = n := by dsimp only [m]; omega
  let D : StageDart (kmswStage u n).nextEdge :=
    (⟨(kmswWindowPatchData u s m).φ d.1.val, by
      have h := (kmswWindowPatchData_rel u s m).edge_bound d.1.val d.1.isLt
      simpa only [hsm] using h⟩, d.2)
  have hhead' : stageEndpoint (kmswStage u n) (edgeFlip _ D) =
      kmswWindowPatchVertexMap u s m
        (stageEndpoint (kmswStage v m) (edgeFlip _ d)) := by
    have h := kmswWindowDartMap_vertex u s m (edgeFlip _ d)
    change (if !d.2 then
      (kmswStage u (s + m)).east ((kmswWindowPatchData u s m).φ d.1.val)
      else (kmswStage u (s + m)).west ((kmswWindowPatchData u s m).φ d.1.val)) =
        kmswWindowPatchVertexMap u s m
          (if !d.2 then (kmswStage v m).east d.1.val
           else (kmswStage v m).west d.1.val) at h
    change (if !d.2 then
      (kmswStage u n).east ((kmswWindowPatchData u s m).φ d.1.val)
      else (kmswStage u n).west ((kmswWindowPatchData u s m).φ d.1.val)) =
        kmswWindowPatchVertexMap u s m
          (if !d.2 then (kmswStage v m).east d.1.val
           else (kmswStage v m).west d.1.val)
    simpa only [hsm] using h
  have htail' : stageEndpoint (kmswStage u n) D =
      kmswWindowPatchVertexMap u s m (stageEndpoint (kmswStage v m) d) := by
    have h := kmswWindowDartMap_vertex u s m d
    simpa only [stageEndpoint, D, kmswWindowDartMap, hsm] using h
  have hD : D = kmswDiskRootDart c k :=
    (kmswDiskRootDart_hit_frame_iff c k D).mp
      ⟨he, hhead'.trans hhead, htail'.trans htail⟩
  exact congrArg Prod.snd hD

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
transported to the KMSW window; not the paper result. The edge image and its
ordered patched endpoints determine exactly one window dart. -/
theorem kmswDiskRootFrame_window_ordered_unique {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1))
    (s : ℕ) (hs : s < kmswDiskFirstHit c k) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let m := n - s
    let v := fun i => u (s + i)
    ∃! d : StageDart (kmswStage v m).nextEdge,
      (kmswWindowPatchData u s m).φ d.1.val = kmswLLCreatedEdge u T ∧
      kmswWindowPatchVertexMap u s m
        (stageEndpoint (kmswStage v m) (edgeFlip _ d)) = activeInitial u T ∧
      kmswWindowPatchVertexMap u s m
        (stageEndpoint (kmswStage v m) d) = activeInitial u (T - 1) := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let m := n - s
  obtain ⟨d, hd⟩ := kmswDiskRootFrame_window_ordered c k s hs
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Prod.ext
  · apply Fin.ext
    exact (kmswWindowPatchData_rel u s m).edge_injective
      e.1.val e.1.isLt d.1.val d.1.isLt (he.1.trans hd.1.symm)
  · exact (kmswDiskRootFrame_window_ordered_side c k s hs e he.1 he.2.1 he.2.2).trans
      (kmswDiskRootFrame_window_ordered_side c k s hs d hd.1 hd.2.1 hd.2.2).symm

end DirectedDistances.KMSW
