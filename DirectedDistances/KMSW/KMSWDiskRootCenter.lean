module

public import DirectedDistances.KMSW.KMSWDiskRootOrderedFrame
public import DirectedDistances.KMSW.CutEquivalenceConverse

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
frame; not the paper result. Its west endpoint is the active initial vertex
at the hit time; its east endpoint is the active initial vertex just before
that time. These are geometric endpoints, not an orientation of the missing -/
theorem kmswDiskRootEdge_endpoints {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let e := kmswLLCreatedEdge u T
    (kmswStage u n).west e = activeInitial u T ∧
      (kmswStage u n).east e = activeInitial u (T - 1) := by
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  have hspec := kmswDiskFirstHit_spec c k
  have hT : 0 < T := hspec.1
  have hTn : T ≤ n := hspec.2.1
  obtain ⟨j, hjT, _, hjcode, hjdrop, _, _, _, _, _⟩ :=
    kmswDiskFirstHit_triangle c k
  have hc : u (T - 1) = 0 := by simpa only [hjT] using hjcode
  have hd : (kmswStage u (T - 1)).UL.dropLast.reverse = [] := by
    have h : (kmswStage u (T - 1)).UL.dropLast = [] := by
      simpa only [hjT] using hjdrop
    rw [h]
    rfl
  have hprev : T - 1 + 1 = T := by omega
  have hid : kmswLLCreatedEdge u T = (kmswStage u (T - 1)).nextEdge + 1 := by
    conv_lhs => rw [← hprev]
    simp [kmswLLCreatedEdge, kmswStage, kmswStep, hc, kmswCodeStep,
      kmswStepOfStep, hd, State.addEdge]
  have hbound : kmswLLCreatedEdge u T < (kmswStage u T).nextEdge := by
    rw [hid, ← hprev]
    simp [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hd, State.addEdge]
  have hstable := kmswStage_endpoints_stable u hTn hbound
  have hwest : (kmswStage u T).west (kmswLLCreatedEdge u T) =
      activeInitial u T := by
    rw [CutConverse.activeInitial_eq, hid, ← hprev]
    simp [act, kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hd,
      State.addEdge]
  have heast : (kmswStage u T).east (kmswLLCreatedEdge u T) =
      activeInitial u (T - 1) := by
    rw [CutConverse.activeInitial_eq, hid, ← hprev]
    simp [act, kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hd,
      State.addEdge]
  exact ⟨hstable.1.trans hwest, hstable.2.trans heast⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
frame; not the paper result. In the west-to-east LL vertex order the endpoint
indices are `ℓ - 2 - k.val` and `ℓ - 1 - k.val`, respectively. Thus the first
of these vertices supplies `x₀`, and the second supplies `x₁`, as ordered in
from the lower-right end, whereas the LL vertex list starts at the west end.
This identifies the finite stage frame, not its transport to an arbitrary
isomorphic representative of the sampled map. -/
theorem kmswDiskRootEdge_boundary_indices {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let S := kmswStage u n
    (llVertices S).length = ℓ ∧
      (llVertices S)[ℓ - 2 - k.val]? = some (activeInitial u T) ∧
      (llVertices S)[ℓ - 1 - k.val]? = some (activeInitial u (T - 1)) := by
  let u := finiteCodeExtend (n := n + 1) c.val
  let S := kmswStage u n
  have hlen : S.LL.length = ℓ - 1 := (kmswDiskFiniteSample_index_bound c k).1
  have hk := k.isLt
  have hne : S.LL ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hvlen : (llVertices S).length = ℓ := by
    rw [llVertices_length S hne, hlen]
    omega
  have hp : S.LL.length - 1 - k.val = ℓ - 2 - k.val := by omega
  have hpnext : S.LL.length - 1 - k.val + 1 = ℓ - 1 - k.val := by omega
  have hf := kmswDiskRootDart_ordered_frame c k
  have he := kmswDiskRootEdge_endpoints c k
  have hw := hf.2.2.1.trans he.1
  have hx := hf.2.2.2.trans he.2
  change (llVertices S)[S.LL.length - 1 - k.val] = _ at hw
  change (llVertices S)[S.LL.length - 1 - k.val + 1] = _ at hx
  refine ⟨hvlen, ?_, ?_⟩
  · have hw' : (llVertices S)[S.LL.length - 1 - k.val]? =
        some (activeInitial u (kmswDiskFirstHit c k)) := by
      rw [List.getElem?_eq_getElem (by rw [hvlen]; omega)]
      exact congrArg some hw
    simpa only [hp] using hw'
  · have hx' : (llVertices S)[S.LL.length - 1 - k.val + 1]? =
        some (activeInitial u (kmswDiskFirstHit c k - 1)) := by
      rw [List.getElem?_eq_getElem (by rw [hvlen]; omega)]
      exact congrArg some hx
    simpa only [hpnext] using hx'

private theorem diskRoot_hit_initial_ne {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    activeInitial u T ≠ activeInitial u (T - 1) := by
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  have hT : 0 < T := (kmswDiskFirstHit_spec c k).1
  obtain ⟨j, hjT, _, hjcode, hjdrop, _, _, _, _, _⟩ :=
    kmswDiskFirstHit_triangle c k
  have hc : u (T - 1) = 0 := by simpa only [hjT] using hjcode
  have hd : (kmswStage u (T - 1)).UL.dropLast.reverse = [] := by
    have h : (kmswStage u (T - 1)).UL.dropLast = [] := by
      simpa only [hjT] using hjdrop
    rw [h]
    rfl
  have hprev : T - 1 + 1 = T := by omega
  have hfresh : activeInitial u T = (kmswStage u (T - 1)).nextVertex := by
    rw [CutConverse.activeInitial_eq, ← hprev]
    simp [act, kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hd,
      State.addEdge]
  have hbound : activeInitial u (T - 1) < (kmswStage u (T - 1)).nextVertex := by
    rw [CutConverse.activeInitial_eq]
    exact (CutConverse.endpoint_bound u (T - 1) _ (act_lt_nextEdge u le_rfl)).1
  change activeInitial u T ≠ activeInitial u (T - 1)
  omega

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
frame; not the paper result. The existing root dart is exactly the dart whose
flipped endpoint is `x₀ = activeInitial u T` and whose endpoint is
`x₁ = activeInitial u (T - 1)`. This characterizes its Boolean side from the
ordered geometric endpoints, without orienting the missing edge -/
theorem kmswDiskRootDart_hit_frame_iff {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let S := kmswStage u n
    ∀ d : StageDart S.nextEdge,
      (d.1.val = kmswLLCreatedEdge u T ∧
        stageEndpoint S (edgeFlip S.nextEdge d) = activeInitial u T ∧
        stageEndpoint S d = activeInitial u (T - 1)) ↔
      d = kmswDiskRootDart c k := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  let S := kmswStage u n
  have he := kmswDiskRootEdge_endpoints c k
  have hne := diskRoot_hit_initial_ne c k
  intro d
  constructor
  · rintro ⟨hedge, htail, _⟩
    apply Prod.ext
    · apply Fin.ext
      exact hedge
    · change d.2 = true
      cases hb : d.2 with
      | true => rfl
      | false =>
        have hx : S.east (kmswLLCreatedEdge u T) = activeInitial u T := by
          simpa [stageEndpoint, edgeFlip, hb, hedge] using htail
        exact False.elim (hne (hx.symm.trans he.2))
  · intro hd
    subst d
    have hf := kmswDiskRootDart_ordered_frame c k
    exact ⟨rfl, hf.1.trans he.1, hf.2.1.trans he.2⟩

end DirectedDistances.KMSW
