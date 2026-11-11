module

public import DirectedDistances.KMSW.HatFaceRotation
public import DirectedDistances.KMSW.KMSWInverse










public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open Quiver

/-- A rooted induced cyclic-order embedding, allowing missing source edges
to become present. Roots here are active stage darts. Hatted-half interface -/
structure RootedInducedEmbedding {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E]
    (N : RootedDirectedMapWithMissing D) (M : RootedDirectedMapWithMissing E) where
  dartMap : D → E
  injective : Function.Injective dartMap
  flip_comm : ∀ d, dartMap (N.map.edgeInv d) = M.map.edgeInv (dartMap d)
  present : ∀ d, ¬ N.map.missing d → ¬ M.map.missing (dartMap d)
  tail_comm : ∀ d, ¬ N.map.missing d → (N.map.tail d ↔ M.map.tail (dartMap d))
  rot_induced : ∀ d, ∃ k : ℕ, 0 < k ∧
    (M.map.rot : E → E)^[k] (dartMap d) = dartMap (N.map.rot d) ∧
    ∀ j : ℕ, 0 < j → j < k →
      (M.map.rot : E → E)^[j] (dartMap d) ∉ Set.range dartMap
  root_comm : dartMap N.root = M.root

/-- Present local darts stay present at the aligned stage. Hatted-half helper -/
theorem hatDartMap_present (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : ¬ (kmswRootedStage (hatCodes w h) m).map.missing d) :
    ¬ (kmswRootedStage w (quadrantRStageTime w h m)).map.missing
      (hatDartMap w h m d) := by
  change ¬ (kmswStage (hatCodes w h) m).present d.1.val = false at hd
  change ¬ (kmswStage w (quadrantRStageTime w h m)).present
    (hatAllEdgeMap w h m d.1.val) = false
  have hp := (hatAll_sim w h m).incidenceSim.present d.1.val d.1.isLt
    (Bool.eq_true_of_not_eq_false hd)
  rw [hp]
  decide

/-- The side bit preserves directed tails of present edges. Hatted-half helper -/
theorem hatDartMap_tail (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : ¬ (kmswRootedStage (hatCodes w h) m).map.missing d) :
    (kmswRootedStage (hatCodes w h) m).map.tail d ↔
      (kmswRootedStage w (quadrantRStageTime w h m)).map.tail
        (hatDartMap w h m d) := by
  have hg := hatDartMap_present w h m d hd
  change ¬ (kmswStage (hatCodes w h) m).present d.1.val = false at hd
  change ¬ (kmswStage w (quadrantRStageTime w h m)).present
    (hatAllEdgeMap w h m d.1.val) = false at hg
  change ((kmswStage (hatCodes w h) m).present d.1.val = true ∧ d.2 = false) ↔
    ((kmswStage w (quadrantRStageTime w h m)).present
      (hatAllEdgeMap w h m d.1.val) = true ∧ d.2 = false)
  rw [Bool.eq_true_of_not_eq_false hd, Bool.eq_true_of_not_eq_false hg]

/-- The active stage roots agree. The original paper root edge `0` is treated
separately by `hat_root_correspondence`. Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_root (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    hatDartMap w h m (kmswRootedStage (hatCodes w h) m).root =
      (kmswRootedStage w (quadrantRStageTime w h m)).root :=
  hatDartMap_active w h m

/-- Inner flipped darts give compatibility with inverse vertex rotation.
Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_rot_symm_of_not_outer (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : (kmswMap (hatCodes w h) m).edgeInv d ∉
      stageOuterWord (hatCodes w h) m) :
    (kmswMap w (quadrantRStageTime w h m)).rot.symm (hatDartMap w h m d) =
      hatDartMap w h m ((kmswMap (hatCodes w h) m).rot.symm d) := by
  have hf := hatDartMap_faceSucc_of_not_outer w h m _ hd
  rw [← hatDartMap_edgeInv] at hf
  simpa only [CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def, CombinatorialMap.edgeInv_invol] using hf

/-- Forward vertex rotation agrees when the flipped successor is inner.
Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_rot_of_not_outer (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : (kmswMap (hatCodes w h) m).edgeInv ((kmswMap (hatCodes w h) m).rot d) ∉
      stageOuterWord (hatCodes w h) m) :
    (kmswMap w (quadrantRStageTime w h m)).rot (hatDartMap w h m d) =
      hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) := by
  have hi := hatDartMap_rot_symm_of_not_outer w h m _ hd
  rw [Equiv.symm_apply_apply] at hi
  exact (kmswMap w (quadrantRStageTime w h m)).rot.eq_symm_apply.mp hi.symm

/-- On inner successor corners, induced rotation has first return time one.
Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_rot_induced_of_not_outer (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : (kmswMap (hatCodes w h) m).edgeInv ((kmswMap (hatCodes w h) m).rot d) ∉
      stageOuterWord (hatCodes w h) m) :
    ∃ k : ℕ, 0 < k ∧
      ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
        (hatDartMap w h m d) = hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
          (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m) := by
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · simpa only [Function.iterate_one] using hatDartMap_rot_of_not_outer w h m d hd
  · intro j hj hjk
    omega

/-- Geometric endpoints, including those of missing edges, commute with the
hatted vertex map. Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_endpoint (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    stageEndpoint (kmswStage w (quadrantRStageTime w h m)) (hatDartMap w h m d) =
      hatAllVertexMap w h m (stageEndpoint (kmswStage (hatCodes w h) m) d) := by
  have hi := (hatAll_sim w h m).incidenceSim.incidence d.1.val d.1.isLt
  cases hb : d.2
  · simpa only [stageEndpoint, hatDartMap, hb, Bool.false_eq_true, ↓reduceIte] using hi.1
  · simpa only [stageEndpoint, hatDartMap, hb, ↓reduceIte] using hi.2

/-- Equality of image endpoint IDs reflects equality of local endpoint IDs,
including for missing edges. Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_endpoint_eq_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d e : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    stageEndpoint (kmswStage w (quadrantRStageTime w h m)) (hatDartMap w h m d) =
        stageEndpoint (kmswStage w (quadrantRStageTime w h m)) (hatDartMap w h m e) ↔
      stageEndpoint (kmswStage (hatCodes w h) m) d =
        stageEndpoint (kmswStage (hatCodes w h) m) e := by
  rw [hatDartMap_endpoint, hatDartMap_endpoint]
  exact ⟨(hatAll_sim w h m).incidenceSim.vertex_injective _ _
    (stageEndpoint_lt_nextVertex _ m d) (stageEndpoint_lt_nextVertex _ m e),
    congrArg (hatAllVertexMap w h m)⟩

/-- Every image dart at an image vertex comes from a dart at that local
vertex, including darts of currently missing edges. Hatted-half helper for -/
theorem hatDartMap_range_at_vertex (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (v : Fin (kmswStage (hatCodes w h) m).nextVertex)
    (e : StageDart (kmswStage w (quadrantRStageTime w h m)).nextEdge) :
    (e ∈ Set.range (hatDartMap w h m) ∧
      stageEndpoint (kmswStage w (quadrantRStageTime w h m)) e =
        hatAllVertexMap w h m v.val) ↔
      ∃ d : StageDart (kmswStage (hatCodes w h) m).nextEdge,
        stageEndpoint (kmswStage (hatCodes w h) m) d = v.val ∧
          hatDartMap w h m d = e := by
  constructor
  · rintro ⟨⟨d, rfl⟩, he⟩
    refine ⟨d, ?_, rfl⟩
    rw [hatDartMap_endpoint] at he
    exact (hatAll_sim w h m).incidenceSim.vertex_injective _ _
      (stageEndpoint_lt_nextVertex _ m d) v.isLt he
  · rintro ⟨d, hd, rfl⟩
    refine ⟨⟨d, rfl⟩, ?_⟩
    rw [hatDartMap_endpoint, hd]

/-- Ambient rotation cycles of image darts reflect exactly the local vertex
cycles. In particular an image dart at a given image vertex comes from that
local vertex. Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_sameCycle_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d e : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    (kmswMap w (quadrantRStageTime w h m)).rot.SameCycle
        (hatDartMap w h m d) (hatDartMap w h m e) ↔
      (kmswMap (hatCodes w h) m).rot.SameCycle d e := by
  rw [kmswMap_rot, kmswMap_rot, stageRot_sameCycle_iff_endpoint_eq,
    stageRot_sameCycle_iff_endpoint_eq]
  exact hatDartMap_endpoint_eq_iff w h m d e

private theorem hat_root_boundary_invariant (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∀ m, (∀ e < (kmswStage (hatCodes w h) m).nextEdge,
        (kmswStage (hatCodes w h) m).east e ≠ 0) ∧
      (∀ e ∈ (kmswStage (hatCodes w h) m).LR,
        (kmswStage (hatCodes w h) m).west e = 0 → e = 0) ∧
      (kmswStage (hatCodes w h) m).LL = [] := by
  intro m
  induction m with
  | zero => simp [kmswStage, kmswInit]
  | succ m ih =>
    let s := kmswStage (hatCodes w h) m
    change (∀ e < s.nextEdge, s.east e ≠ 0) ∧
      (∀ e ∈ s.LR, s.west e = 0 → e = 0) ∧ s.LL = [] at ih
    have ha := (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) m).1
    change s.active < s.nextEdge at ha
    have hv : s.nextVertex ≠ 0 := by
      have hb := (kmswStage_endpoints_lt_nextVertex (hatCodes w h) m s.active ha).1
      change s.west s.active < s.nextVertex at hb
      omega
    have heast : s.east s.active ≠ 0 := ih.1 _ ha
    change (∀ e < (kmswStepOfStep s (kmswCodeStep (hatCodes w h m))).nextEdge,
        (kmswStepOfStep s (kmswCodeStep (hatCodes w h m))).east e ≠ 0) ∧
      (∀ e ∈ (kmswStepOfStep s (kmswCodeStep (hatCodes w h m))).LR,
        (kmswStepOfStep s (kmswCodeStep (hatCodes w h m))).west e = 0 → e = 0) ∧
      (kmswStepOfStep s (kmswCodeStep (hatCodes w h m))).LL = []
    cases hc : kmswCodeStep (hatCodes w h m) with
    | left =>
      have hn := noFreshLeftSource_hatCodes w h m hc
      cases hp : s.UL.dropLast.reverse with
      | nil => exact (hn hp).elim
      | cons a as =>
        simp only [kmswStepOfStep, hp, State.addEdge]
        refine ⟨?_, ?_, ih.2.2⟩
        · intro e he
          by_cases heq : e = s.nextEdge
          · simp only [heq, ↓reduceIte, ne_eq]
            exact heast
          · simp only [heq, ↓reduceIte]
            exact ih.1 e (by omega)
        · intro e he he0
          have hb : e < s.nextEdge :=
            (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) m).2 e (by
              simp only [List.mem_append]; exact Or.inr he)
          simp only [ne_of_lt hb, ↓reduceIte] at he0
          exact ih.2.1 e he he0
    | up =>
      simp only [kmswStepOfStep, State.addEdge]
      refine ⟨?_, ?_, ih.2.2⟩
      · intro e he
        by_cases h1 : e = s.nextEdge + 1
        · simp only [h1, ↓reduceIte, ne_eq]
          exact heast
        · by_cases h0 : e = s.nextEdge
          · simp only [h0, Nat.ne_add_one, ↓reduceIte, ne_eq]
            exact hv
          · simp only [h1, h0, ↓reduceIte]
            exact ih.1 e (by omega)
      · intro e he he0
        have hb : e < s.nextEdge :=
          (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) m).2 e (by
            simp only [List.mem_append]; exact Or.inr he)
        have hb1 : e ≠ s.nextEdge + 1 := by omega
        simp only [ne_of_lt hb, hb1, ↓reduceIte] at he0
        exact ih.2.1 e he he0
    | down =>
      cases hp : s.UR with
      | cons a as => simpa only [kmswStepOfStep, hp] using ih
      | nil =>
        simp only [kmswStepOfStep, hp, State.addEdge, List.mem_append,
          List.mem_singleton]
        refine ⟨?_, ?_, ih.2.2⟩
        · intro e he
          by_cases heq : e = s.nextEdge
          · simp only [heq, ↓reduceIte, ne_eq]
            exact hv
          · simp only [heq, ↓reduceIte]
            exact ih.1 e (by omega)
        · intro e he he0
          rcases he with he | rfl
          · have hb : e < s.nextEdge :=
              (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h) m).2 e (by
                simp only [List.mem_append]; exact Or.inr he)
            simp only [ne_of_lt hb, ↓reduceIte] at he0
            exact ih.2.1 e he he0
          · simp only [↓reduceIte] at he0
            exact (heast he0).elim

private theorem hat_root_outer_corner (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd0 : stageEndpoint (kmswStage (hatCodes w h) m) d = 0)
    (hd : (kmswMap (hatCodes w h) m).edgeInv d ∈ stageOuterWord (hatCodes w h) m) :
    d.1.val = 0 ∧ d.2 = false := by
  have hi := hat_root_boundary_invariant w h m
  cases hb : d.2
  · have hv : (kmswStage (hatCodes w h) m).west d.1.val = 0 := by
      simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using hd0
    refine ⟨?_, rfl⟩
    simp only [stageOuterWord, List.mem_append, or_assoc] at hd
    rcases hd with hUL | hUR | hLR | hLL
    · obtain ⟨e, _, he⟩ := (stageDarts_mem _ _ _ _ _).mp hUL
      have hs := congrArg Prod.snd he
      change (!d.2) = false at hs
      rw [hb] at hs
      contradiction
    · obtain ⟨e, _, he⟩ := (stageDarts_mem _ _ _ _ _).mp hUR
      have hs := congrArg Prod.snd he
      change (!d.2) = false at hs
      rw [hb] at hs
      contradiction
    · obtain ⟨e, he, heq⟩ := (stageDarts_mem _ _ _ _ _).mp hLR
      have hid : d.1.val = e := congrArg (fun x => x.1.val) heq
      rw [hid] at hv
      exact hid.trans (hi.2.1 e (List.mem_reverse.mp he) hv)
    · obtain ⟨e, he, _⟩ := (stageDarts_mem _ _ _ _ _).mp hLL
      rw [hi.2.2] at he
      simp only [List.reverse_nil, List.not_mem_nil] at he
  · have hv : (kmswStage (hatCodes w h) m).east d.1.val = 0 := by
      simpa only [stageEndpoint, hb, ↓reduceIte] using hd0
    exact (hi.1 _ d.1.isLt hv).elim

private theorem finite_image_first_return {D E : Type*} [Finite E]
    (ρ : Equiv.Perm E) (i : D → E) (d : D) :
    ∃ k : ℕ, 0 < k ∧ (∃ e, i e = (ρ : E → E)^[k] (i d)) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i := by
  classical
  obtain ⟨n, hn, _, he⟩ := (Equiv.Perm.SameCycle.refl ρ (i d)).exists_pow_eq''
  have hex : ∃ n : ℕ, 0 < n ∧ (ρ : E → E)^[n] (i d) ∈ Set.range i :=
    ⟨n, hn, d, he.symm⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro j hj hjk hmem
  exact Nat.find_min hex hjk ⟨hj, hmem⟩

/-- At the original root vertex, the ambient rotation first returns to the
image at exactly the local successor, even across the outer corner. Missing
geometric darts are included in the excluded image. Hatted-half helper for -/
theorem hatDartMap_rot_induced_at_root (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : stageEndpoint (kmswStage (hatCodes w h) m) d = 0) :
    ∃ k : ℕ, 0 < k ∧
      ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
        (hatDartMap w h m d) = hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
          (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m) := by
  classical
  let σ := (kmswMap (hatCodes w h) m).rot
  let ρ := (kmswMap w (quadrantRStageTime w h m)).rot
  let i := hatDartMap w h m
  by_cases ho : (kmswMap (hatCodes w h) m).edgeInv (σ d) ∈
      stageOuterWord (hatCodes w h) m
  · have hσd : stageEndpoint (kmswStage (hatCodes w h) m) (σ d) = 0 := by
      have hc : σ.SameCycle d (σ d) := ⟨1, rfl⟩
      exact ((stageRot_sameCycle_iff_endpoint_eq _ m d (σ d)).mp hc).symm.trans hd
    have hcorner := hat_root_outer_corner w h m (σ d) hσd ho
    obtain ⟨k, hk, ⟨e, he⟩, hgap⟩ := finite_image_first_return ρ i d
    refine ⟨k, hk, ?_, hgap⟩
    have hce : ρ.SameCycle (i d) (i e) := by
      rw [he]
      exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl ρ (i d))
    have hlocal := (hatDartMap_sameCycle_iff w h m d e).mp hce
    have he0 : stageEndpoint (kmswStage (hatCodes w h) m) e = 0 :=
      ((stageRot_sameCycle_iff_endpoint_eq _ m d e).mp hlocal).symm.trans hd
    have hetarget : e = σ d := by
      by_cases heo : (kmswMap (hatCodes w h) m).edgeInv e ∈
          stageOuterWord (hatCodes w h) m
      · have hecorner := hat_root_outer_corner w h m e he0 heo
        exact Prod.ext (Fin.ext (hecorner.1.trans hcorner.1.symm))
          (hecorner.2.trans hcorner.2.symm)
      · have hr : ρ.symm (i e) = i (σ.symm e) :=
          hatDartMap_rot_symm_of_not_outer w h m e heo
        cases k with
        | zero => omega
        | succ t =>
          have hpred : (ρ : _ → _)^[t] (i d) = i (σ.symm e) := by
            calc
              _ = ρ.symm ((ρ : _ → _)^[t + 1] (i d)) := by
                rw [Function.iterate_succ_apply', Equiv.symm_apply_apply]
              _ = ρ.symm (i e) := congrArg ρ.symm he.symm
              _ = i (σ.symm e) := hr
          cases t with
          | zero =>
              have hde : d = σ.symm e := (hatDartMap_injective w h m) hpred
              exact (σ.eq_symm_apply.mp hde).symm
          | succ t =>
              exact (hgap (t + 1) (by omega) (by omega)
                ⟨σ.symm e, hpred.symm⟩).elim
    exact he.symm.trans (congrArg i hetarget)
  · exact hatDartMap_rot_induced_of_not_outer w h m d ho

/-- At a vertex with no outer-face corner, induced rotation has return time
one at every dart. The premise excludes outer corners geometrically, rather
than assuming a rotation comparison. Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_rot_induced_of_inner_vertex (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge)
    (hd : ∀ e ∈ stageOuterWord (hatCodes w h) m,
      stageEndpoint (kmswStage (hatCodes w h) m)
          ((kmswMap (hatCodes w h) m).edgeInv e) ≠
        stageEndpoint (kmswStage (hatCodes w h) m) d) :
    ∃ k : ℕ, 0 < k ∧
      ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
        (hatDartMap w h m d) = hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
          (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m) := by
  apply hatDartMap_rot_induced_of_not_outer
  intro ho
  have hn := hd _ ho
  rw [CombinatorialMap.edgeInv_invol] at hn
  apply hn
  exact ((stageRot_sameCycle_iff_endpoint_eq (hatCodes w h) m d
    ((kmswMap (hatCodes w h) m).rot d)).mp ⟨1, rfl⟩).symm

/-- The dart maps commute with inclusion into any later aligned stage.
Hatted-half helper for `lem-quad-kmsw` -/
theorem hatDartMap_compatible (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m n : ℕ) (hmn : m ≤ n)
    (d : StageDart (kmswStage (hatCodes w h) m).nextEdge) :
    hatDartMap w h n
        (outerSucc_castDart (kmswStage_nextEdge_mono (hatCodes w h) hmn) d) =
      outerSucc_castDart
        (kmswStage_nextEdge_mono w (quadrantRStageTime_mono w h hmn))
        (hatDartMap w h m d) := by
  apply Prod.ext
  · exact Fin.ext (hatAllEdgeMap_eq_of_le w h m n d.1.val hmn d.1.isLt)
  · rfl

/-- Stage images exhaust reachable vertices, reachable present edges, and
triangles with the source's three-corner reachability condition. The edge
witness is present already at the witnessing stage. Hatted-half helper for -/
theorem hatDartMap_cofinal (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    (∀ v : PresentVertex w, Reachable (⟨0⟩ : PresentVertex w) v →
      ∃ m a, a < (kmswStage (hatCodes w h) m).nextVertex ∧
        hatAllVertexMap w h m a = v.id) ∧
    (∀ e : ℕ, EdgePresent w e →
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩ →
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e⟩ →
      ∃ m a, a < (kmswStage (hatCodes w h) m).nextEdge ∧
        (kmswStage (hatCodes w h) m).present a = true ∧
        hatAllEdgeMap w h m a = e) ∧
    (∀ s : GlobalHatTriSrc w, ∃ m t,
      t ∈ (kmswStage (hatCodes w h) m).triangles ∧
      (hatAllEdgeMap w h m t.1, hatAllEdgeMap w h m t.2.1,
        hatAllEdgeMap w h m t.2.2) = s.1) := by
  obtain ⟨V, E, _, hV, hE, _, _⟩ := hatExplicitGraphFaceIso w h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨a, ha⟩ := V.surjective ⟨v, hv⟩
    obtain ⟨m, hm⟩ := a.property
    refine ⟨m, a.1.id, hm, ?_⟩
    have hi := congrArg (fun x => x.1.id) ha
    rw [hV a, hatLimitVertexMap_eq_stage w h m a.1.id hm] at hi
    exact hi
  · intro e he hw heast
    obtain ⟨a, ha⟩ := E.surjective ⟨e, he, hw, heast⟩
    obtain ⟨m, hm, hp⟩ := a.property
    refine ⟨m, a.val, hm, hp, ?_⟩
    have hi := congrArg Subtype.val ha
    rw [hE a, hatLimitEdgeMap_eq_stage w h m a.val hm] at hi
    exact hi
  · intro s
    obtain ⟨t, ht⟩ := (hatSourceFaceEquiv w h).surjective s
    obtain ⟨m, hm⟩ := t.property
    refine ⟨m, t.val, hm, ?_⟩
    have hi := hatSourceFaceEquiv_compatible w h t
    rw [ht] at hi
    simp only [hatExplicitEdgeEquiv_apply] at hi
    have hb := triBound_stage (hatCodes w h) m t.val hm
    rw [hatLimitEdgeMap_eq_stage w h m _ hb.1,
      hatLimitEdgeMap_eq_stage w h m _ hb.2.1,
      hatLimitEdgeMap_eq_stage w h m _ hb.2.2] at hi
    exact hi.symm

/- Remaining non-root boundary obligation. The root and interior-vertex

w : ℕ → Fin 3
h : HasFlowLineHits w
m : ℕ
d : StageDart (kmswStage (hatCodes w h) m).nextEdge
hd0 : stageEndpoint (kmswStage (hatCodes w h) m) d ≠ 0
hd : (kmswMap (hatCodes w h) m).edgeInv ((kmswMap (hatCodes w h) m).rot d) ∈
  stageOuterWord (hatCodes w h) m
⊢ ∃ k : ℕ, 0 < k ∧
    ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[k]
      (hatDartMap w h m d) = hatDartMap w h m ((kmswMap (hatCodes w h) m).rot d) ∧
    ∀ j : ℕ, 0 < j → j < k →
      ((kmswMap w (quadrantRStageTime w h m)).rot : _ → _)^[j]
        (hatDartMap w h m d) ∉ Set.range (hatDartMap w h m)

The image-at-vertex assertion is `hatDartMap_range_at_vertex`. The unresolved
point is the cyclic order of the different outer corners at a non-root
boundary vertex, including currently missing geometric edges. The finite
first-return lemma supplies existence and exclusion, but does not identify
the returned local dart with the local successor at such a vertex.

No preservation induction on step kinds is claimed for this residual case.
Its ordinary-step branches are up, existing-predecessor left, and down
(activation or pendant); the exit branch additionally requires composition
with the intervening excursion. Local fresh-left is ruled out by
`noFreshLeftSource_hatCodes`. Thus this work has not isolated the residual
obligation to one step kind.
Until this is proved, no `hatDartMap_inducedEmbedding` is asserted here. -/

end DirectedDistances.KMSW
