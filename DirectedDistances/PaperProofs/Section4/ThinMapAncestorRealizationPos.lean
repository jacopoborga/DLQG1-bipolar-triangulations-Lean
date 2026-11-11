module

public import DirectedDistances.PaperProofs.Section4.ThinMapAncestorRealizationFinal
import DirectedDistances.KMSW.HatInducedExit
import DirectedDistances.KMSW.StageInfiniteOutgoingOrder

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

Positive-level permanent-ID embeddings. The geometric identification obligations -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver
open scoped Classical

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual cut half, retaining its dependent boundary lengths and dart count. -/
@[expose] noncomputable def ancestorPosHalfRep
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (a : ThinMapSide) :
    KMSWMapRep (match a with | .left => ℓ | .right => m)
      (match a with | .left => m | .right => r)
      (match a with | .left => (cutLRep R hR).1 | .right => (cutRRep R hR).1) :=
  match a with
  | .left => (cutLRep R hR).2
  | .right => (cutRRep R hR).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual half dart map into the uncut representative. -/
@[expose] noncomputable def ancestorPosDartMap
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (a : ThinMapSide) :
    Fin (ancestorPosHalfRep R hR a).dartCount → Fin R.dartCount :=
  match a with
  | .left => cutLRepDartMap R hR
  | .right => cutRRepDartMap R hR

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual half vertex map into the uncut representative. -/
@[expose] noncomputable def ancestorPosVertexMap
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (a : ThinMapSide) :
    MapVertex (ancestorPosHalfRep R hR a).B.map → MapVertex R.B.map :=
  match a with
  | .left => cutLRepVertexMap R hR
  | .right => cutRRepVertexMap R hR

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both concrete half maps are injective and preserve the two dart endpoints. -/
theorem ancestorPos_embedding_fields
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (a : ThinMapSide) :
    Function.Injective (ancestorPosDartMap R hR a) ∧
    Function.Injective (ancestorPosVertexMap R hR a) ∧
    ∀ d,
      ancestorPosVertexMap R hR a
          (dartTailVertex (ancestorPosHalfRep R hR a).B.map d) =
        dartTailVertex R.B.map (ancestorPosDartMap R hR a d) ∧
      ancestorPosVertexMap R hR a
          (dartHeadVertex (ancestorPosHalfRep R hR a).B.map d) =
        dartHeadVertex R.B.map (ancestorPosDartMap R hR a d) := by
  cases a with
  | left =>
      refine ⟨(cutLRep_embedding_fields R hR).1,
        (cutLRep_embedding_fields R hR).2.1, ?_⟩
      intro d
      let P := selectedGeodesicOfLen R.B x hR
      let B := pathCutLeftHalfBase R.B P
      let I := (B.transportIso (Fintype.equivFin _)).symm
      constructor
      · exact (congrArg (pathCutLeftHalfVertexMap R.B P)
          (I.vertexEquiv_dartTailVertex d)).trans
            (pathCutLeftHalfVertexMap_dartTailVertex R.B P (I.toEquiv d))
      · exact (congrArg (pathCutLeftHalfVertexMap R.B P)
          (I.vertexEquiv_dartHeadVertex d)).trans
            (pathCutLeftHalfVertexMap_dartHeadVertex R.B P (I.toEquiv d))
  | right =>
      refine ⟨(cutRRep_embedding_fields R hR).1,
        (cutRRep_embedding_fields R hR).2.1, ?_⟩
      intro d
      let P := selectedGeodesicOfLen R.B x hR
      let B := pathCutRightHalfBase R.B P
      let I := (B.transportIso (Fintype.equivFin _)).symm
      constructor
      · exact (congrArg (pathCutRightHalfVertexMap R.B P)
          (I.vertexEquiv_dartTailVertex d)).trans
            (pathCutRightHalfVertexMap_dartTailVertex R.B P (I.toEquiv d))
      · exact (congrArg (pathCutRightHalfVertexMap R.B P)
          (I.vertexEquiv_dartHeadVertex d)).trans
            (pathCutRightHalfVertexMap_dartHeadVertex R.B P (I.toEquiv d))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent vertex ID of a concrete half vertex in an actual stage. -/
@[expose] noncomputable def ancestorPosVertexId
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (a : ThinMapSide) (v : MapVertex (ancestorPosHalfRep R hR a).B.map) : ℕ :=
  (stageMapVertex w t (cutMapIsoVertexEquiv I (ancestorPosVertexMap R hR a v))).id

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent geometric dart ID, including its endpoint side. -/
@[expose] noncomputable def ancestorPosDartId
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (a : ThinMapSide) (d : Fin (ancestorPosHalfRep R hR a).dartCount) : ℕ × Bool :=
  stageLimitDart w t (I.toEquiv (ancestorPosDartMap R hR a d))

private theorem ancestorPos_firstReturn_forward
    {A B : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (τ : Equiv.Perm B) (f : A → B) (hf : Function.Injective f)
    (hn : ∀ d, ∃ k : ℕ, 0 < k ∧ (τ : B → B)^[k] (f d) = f (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (τ : B → B)^[j] (f d) ∉ Set.range f)
    (U : Set A) (d e : U) (k : ℕ) (hk : 0 < k)
    (he : (σ : A → A)^[k] d.1 = e.1)
    (hgap : ∀ j : ℕ, 0 < j → j < k → (σ : A → A)^[j] d.1 ∉ U) :
    ∃ m : ℕ, 0 < m ∧ (τ : B → B)^[m] (f d.1) = f e.1 ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U := by
  have hex : ∀ n, n ≤ k → ∃ m : ℕ, n ≤ m ∧ (n = 0 → m = 0) ∧
      (τ : B → B)^[m] (f d.1) = f ((σ : A → A)^[n] d.1) ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨0, le_rfl, fun _ => rfl, rfl, fun j hj hjm => by omega⟩
    | succ n ih =>
        intro hnk
        obtain ⟨m, hnm, hm0, hm, havoid⟩ := ih (by omega)
        obtain ⟨l, hl, hlstep, hlavoid⟩ := hn ((σ : A → A)^[n] d.1)
        refine ⟨m + l, by omega, by omega, ?_, ?_⟩
        · rw [Nat.add_comm m l, Function.iterate_add_apply, hm, hlstep]
          rw [Function.iterate_succ_apply']
        · intro j hj hjml hmem
          by_cases hjm : j < m
          · exact havoid j hj hjm hmem
          · by_cases hjme : j = m
            · subst j
              obtain ⟨a, ha, hea⟩ := hmem
              have hnpos : 0 < n := by
                by_contra h
                have hn0 : n = 0 := by omega
                have := hm0 hn0
                omega
              apply hgap n hnpos (by omega)
              exact (hf (hea.trans hm)).symm ▸ ha
            · have hjpos : 0 < j - m := by omega
              have hjlt : j - m < l := by omega
              apply hlavoid (j - m) hjpos hjlt
              obtain ⟨a, _, hea⟩ := hmem
              refine ⟨a, ?_⟩
              have hjdecomp : j - m + m = j := by omega
              have hh := Function.iterate_add_apply (τ : B → B) (j - m) m (f d.1)
              rw [hjdecomp, hm] at hh
              exact hea.trans hh
  obtain ⟨m, hkm, _, hm, havoid⟩ := hex k le_rfl
  exact ⟨m, by omega, hm.trans (congrArg f he), havoid⟩

private theorem ancestorPos_firstReturn_image_iff
    {A B : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (τ : Equiv.Perm B) (f : A → B) (hf : Function.Injective f)
    (hn : ∀ d, ∃ k : ℕ, 0 < k ∧ (τ : B → B)^[k] (f d) = f (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (τ : B → B)^[j] (f d) ∉ Set.range f)
    (U : Set A) (d e : U) :
    (∃ k : ℕ, 0 < k ∧ (σ : A → A)^[k] d.1 = e.1 ∧
      ∀ j : ℕ, 0 < j → j < k → (σ : A → A)^[j] d.1 ∉ U) ↔
    (∃ m : ℕ, 0 < m ∧ (τ : B → B)^[m] (f d.1) = f e.1 ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U) := by
  classical
  constructor
  · rintro ⟨k, hk, he, hgap⟩
    exact ancestorPos_firstReturn_forward σ τ f hf hn U d e k hk he hgap
  · rintro ⟨l, hl, hlend, hlgap⟩
    let k := firstReturnTime σ U d
    let z := firstReturn σ U d
    have hs := firstReturnTime_spec σ U d
    have hc := firstReturn_characterization σ U d
    obtain ⟨m, hm, he, hgap⟩ :=
      ancestorPos_firstReturn_forward σ τ f hf hn U d z k hs.1 hc.1 hc.2
    have hml : m = l := by
      apply Nat.le_antisymm
      · by_contra h
        exact hgap l hl (by omega) ⟨e.1, e.2, hlend.symm⟩
      · by_contra h
        exact hlgap m hm (by omega) ⟨z.1, z.2, he.symm⟩
    rw [hml] at he
    have hz : z.1 = e.1 := hf (he.symm.trans hlend)
    exact ⟨k, hs.1, hc.1.trans hz, hc.2⟩

section StageEmbedding

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
  (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent vertex and dart ID maps are injective. -/
theorem ancestorPos_ids_injective :
    Function.Injective (ancestorPosVertexId w t R hR I a) ∧
      Function.Injective (ancestorPosDartId w t R hR I a) := by
  constructor
  · intro u v h
    apply (ancestorPos_embedding_fields R hR a).2.1
    apply (cutMapIsoVertexEquiv I).injective
    apply stageMapVertex_injective w t
    exact congrArg StagePresentVertex.mk h
  · exact (stageLimitDart w t).injective.comp
      (I.toEquiv.injective.comp (ancestorPos_embedding_fields R hR a).1)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both endpoints agree with permanent geometric endpoints, including flipped darts. -/
theorem ancestorPos_ids_endpoints (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    ancestorPosVertexId w t R hR I a
        (dartTailVertex (ancestorPosHalfRep R hR a).B.map d) =
      (if (ancestorPosDartId w t R hR I a d).2 then
        edgeEast w (ancestorPosDartId w t R hR I a d).1 else
        edgeWest w (ancestorPosDartId w t R hR I a d).1) ∧
    ancestorPosVertexId w t R hR I a
        (dartHeadVertex (ancestorPosHalfRep R hR a).B.map d) =
      (if (ancestorPosDartId w t R hR I a d).2 then
        edgeWest w (ancestorPosDartId w t R hR I a d).1 else
        edgeEast w (ancestorPosDartId w t R hR I a d).1) := by
  have ht := (ancestorPos_embedding_fields R hR a).2.2 d
  dsimp only [ancestorPosVertexId, ancestorPosDartId]
  rw [ht.1, ht.2, (cutMapIsoVertexEquiv_endpoints I _).1,
    (cutMapIsoVertexEquiv_endpoints I _).2, stageMapVertex_tail]
  change (_ = _) ∧ (stageEndpoint (kmswStage w t)
    (edgeFlip _ (I.toEquiv (ancestorPosDartMap R hR a d))) = _)
  change (_ = _) ∧
    ((if !(I.toEquiv (ancestorPosDartMap R hR a d)).2 then
      (kmswStage w t).east (I.toEquiv (ancestorPosDartMap R hR a d)).1.val else
      (kmswStage w t).west (I.toEquiv (ancestorPosDartMap R hR a d)).1.val) = _)
  dsimp only [stageEndpoint, stageLimitDart, Function.Embedding.coeFn_mk]
  rw [(edge_endpoints_eq w (I.toEquiv (ancestorPosDartMap R hR a d)).1.isLt).1,
    (edge_endpoints_eq w (I.toEquiv (ancestorPosDartMap R hR a d)).1.isLt).2]
  have flip (b : Bool) (u v : ℕ) :
      (if !b then u else v) = (if b then v else u) := by
    cases b <;> rfl
  exact ⟨rfl, flip _ _ _⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The half dart embedding preserves the opposite dart with the same edge ID. -/
theorem ancestorPos_ids_opposite (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    ancestorPosDartId w t R hR I a ((ancestorPosHalfRep R hR a).B.map.edgeInv d) =
      ((ancestorPosDartId w t R hR I a d).1,
        !(ancestorPosDartId w t R hR I a d).2) := by
  have he : ancestorPosDartMap R hR a
      ((ancestorPosHalfRep R hR a).B.map.edgeInv d) =
        R.B.map.edgeInv (ancestorPosDartMap R hR a d) := by
    cases a with
    | left => exact (cutLRep_embedding_fields R hR).2.2.1 d
    | right => exact (cutRRep_embedding_fields R hR).2.2.1 d
  dsimp only [ancestorPosDartId]
  rw [he, I.edgeInv_comm]
  rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The concrete half orientation is the present permanent edge with false dart side. -/
theorem ancestorPos_ids_oriented (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    (ancestorPosHalfRep R hR a).B.map.tail d ↔
      EdgePresent w (ancestorPosDartId w t R hR I a d).1 ∧
        (ancestorPosDartId w t R hR I a d).2 = false := by
  let e := ancestorPosDartMap R hR a d
  have hp : (kmswStage w t).present (I.toEquiv e).1.val = true := by
    have hn : ¬ (kmswStageDirectedMap w t).missing (I.toEquiv e) := by
      intro h
      exact R.B.noMissingDarts e ((I.missing_iff e).mp h)
    change ¬ (kmswStage w t).present (I.toEquiv e).1.val = false at hn
    cases he : (kmswStage w t).present (I.toEquiv e).1.val <;> simp_all
  have hor : (ancestorPosHalfRep R hR a).B.map.tail d ↔ R.B.map.tail e := by
    cases a with
    | left => exact (cutLRep_embedding_fields R hR).2.2.2.1 d
    | right => exact (cutRRep_embedding_fields R hR).2.2.2.1 d
  rw [hor, ← I.tail_iff]
  change (_ = true ∧ (I.toEquiv e).2 = false) ↔
    (EdgePresent w (I.toEquiv e).1.val ∧ (I.toEquiv e).2 = false)
  simp only [hp, EdgePresent.of_stage_present (I.toEquiv e).1.isLt hp, true_and]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The concrete half source maps to the source of the uncut representative. -/
theorem ancestorPos_source_map :
    ancestorPosVertexMap R hR a (ancestorPosHalfRep R hR a).B.source = R.B.source := by
  cases a with
  | left => exact Option.some.inj (cutLRep_boundaryTarget_map R hR 0)
  | right => exact Option.some.inj (cutRRep_boundaryTarget_map R hR 0)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The half ancestor rotation is first return of the infinite rotation to its
actual permanent dart image. No geometric half-image equality is assumed. -/
theorem ancestorPos_rotation_image
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v : MapVertex (ancestorPosHalfRep R hR a).B.map)
    (d e : selectedDarts (presentation (ancestorPosHalfRep R hR a) a v)) :
    truncationRelation (presentation (ancestorPosHalfRep R hR a) a v)
        .rotation (.inr d) (.inr e) ↔
      ∃ j : ℕ, 0 < j ∧
        (kmswInfRot w hfin : _ → _)^[j] (ancestorPosDartId w t R hR I a d.1) =
          ancestorPosDartId w t R hR I a e.1 ∧
        ∀ i : ℕ, 0 < i → i < j →
          (kmswInfRot w hfin : _ → _)^[i] (ancestorPosDartId w t R hR I a d.1) ∉
            ancestorPosDartId w t R hR I a ''
              selectedDarts (presentation (ancestorPosHalfRep R hR a) a v) := by
  have hhalf : ∀ d, ∃ j : ℕ, 0 < j ∧
      (R.B.map.rot : _ → _)^[j] (ancestorPosDartMap R hR a d) =
        ancestorPosDartMap R hR a ((ancestorPosHalfRep R hR a).B.map.rot d) ∧
      ∀ i : ℕ, 0 < i → i < j →
        (R.B.map.rot : _ → _)^[i] (ancestorPosDartMap R hR a d) ∉
          Set.range (ancestorPosDartMap R hR a) := by
    cases a with
    | left => exact (cutLRep_embedding_fields R hR).2.2.2.2
    | right => exact (cutRRep_embedding_fields R hR).2.2.2.2
  have hiso : ∀ d, ∃ j : ℕ, 0 < j ∧
      (stageRot w t : _ → _)^[j] (I.toEquiv d) = I.toEquiv (R.B.map.rot d) ∧
      ∀ i : ℕ, 0 < i → i < j →
        (stageRot w t : _ → _)^[i] (I.toEquiv d) ∉ Set.range I.toEquiv := by
    intro d
    exact ⟨1, by omega, (I.rot_comm d).symm, fun i hi hij => by omega⟩
  have hstage := hatExit_induced_rotation_comp
    (ancestorPosHalfRep R hR a).B.map.rot R.B.map.rot (stageRot w t)
    (ancestorPosDartMap R hR a) I.toEquiv I.toEquiv.injective hhalf hiso
  have hlimit : ∀ d : StageDart (kmswStage w t).nextEdge,
      ∃ j : ℕ, 0 < j ∧
        (kmswInfRot w hfin : _ → _)^[j] (stageLimitDart w t d) =
          stageLimitDart w t (stageRot w t d) ∧
        ∀ i : ℕ, 0 < i → i < j →
          (kmswInfRot w hfin : _ → _)^[i] (stageLimitDart w t d) ∉
            Set.range (stageLimitDart w t) := by
    intro d
    obtain ⟨j, hj, he, hg⟩ := kmswInfRot_firstReturn_stage w hfin t d
    refine ⟨j, hj, ?_, ?_⟩
    · simpa only [stageLimitDart, Function.Embedding.coeFn_mk, ← Equiv.Perm.coe_pow]
        using he
    · intro i hi hij hmem
      obtain ⟨b, hb⟩ := hmem
      have hge : (kmswStage w t).nextEdge ≤
          ((kmswInfRot w hfin : _ → _)^[i] (stageLimitDart w t d)).1 := by
        simpa only [stageLimitDart, Function.Embedding.coeFn_mk, ← Equiv.Perm.coe_pow]
          using hg i hi hij
      rw [← hb] at hge
      exact (Nat.not_le_of_lt b.1.isLt) hge
  have hfull := hatExit_induced_rotation_comp
    (ancestorPosHalfRep R hR a).B.map.rot (stageRot w t) (kmswInfRot w hfin)
    (I.toEquiv ∘ ancestorPosDartMap R hR a) (stageLimitDart w t)
    (stageLimitDart w t).injective hstage hlimit
  exact ancestorPos_firstReturn_image_iff (ancestorPosHalfRep R hR a).B.map.rot
    (kmswInfRot w hfin) (ancestorPosDartId w t R hR I a)
    (ancestorPos_ids_injective w t R hR I a).2 hfull _ d e

end StageEmbedding

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An ancestor is the target or the tail of a selected geometric dart. -/
theorem ancestorPos_ancestor_tail_or_target (H : HalfTruncationRep)
    (v : ancestors H) :
    v.1 = H.target ∨ ∃ d : selectedDarts H,
      dartTailVertex H.rep.B.map d.1 = v.1 := by
  rcases v.2.cases_head with h | ⟨z, hz, hzt⟩
  · exact Or.inl h
  · obtain ⟨d, _, _, hd, he⟩ := hz
    have ht : dartTailVertex H.rep.B.map d = v.1 := hd
    have hh : dartHeadVertex H.rep.B.map d = z := he
    refine Or.inr ⟨⟨d, ?_, ?_⟩, ht⟩
    · rw [ht]
      exact v.2
    · rw [hh]
      exact hzt

section Geometric

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
  (P : InfinitePresentPath w ⟨0⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A geometric ancestor is the target or the west endpoint of a selected dart.
The latter witness retains its side edge and present orientation. -/
theorem ancestorPos_geometric_tail_or_target (a : ThinMapSide) (s : ℕ)
    (v : sourceAncestorVertices w hfin hL htrans hR P a s) :
    v.1 = thinMapBoundaryVertex w hfin hL htrans hR a s ∨
      ∃ d : sourceAncestorDarts w hfin hL htrans hR P a s,
        d.1.2 = false ∧ edgeWest w d.1.1 = v.1 := by
  rcases v.2.2.cases_head with h | ⟨z, hz, hzt⟩
  · exact Or.inl h
  · obtain ⟨e, hes, hp, hw, he⟩ := hz
    have ht : edgeWest w e ∈ sourceAncestorVertices w hfin hL htrans hR P a s :=
      hw.symm ▸ v.2
    have hh : edgeEast w e ∈ sourceAncestorVertices w hfin hL htrans hR P a s :=
      ⟨(sideEdges_endpoints w hfin hL htrans hR P a hes).2, he.symm ▸ hzt⟩
    exact Or.inr ⟨⟨(e, false), hes, ht, hh⟩, rfl, hw⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Dart-image equality and the target identity already force vertex-image equality.
Thus vertex surjectivity is not a separate geometric identification obligation. -/
theorem ancestorPos_vertices_image_of_darts
    (H : HalfTruncationRep) (a : ThinMapSide) (s : ℕ)
    (F : MapVertex H.rep.B.map → ℕ) (f : Fin H.rep.dartCount → ℕ × Bool)
    (htail : ∀ d, F (dartTailVertex H.rep.B.map d) =
      if (f d).2 then edgeEast w (f d).1 else edgeWest w (f d).1)
    (htarget : F H.target = thinMapBoundaryVertex w hfin hL htrans hR a s)
    (hdarts : f '' selectedDarts H = sourceAncestorDarts w hfin hL htrans hR P a s) :
    F '' ancestors H = sourceAncestorVertices w hfin hL htrans hR P a s := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases ancestorPos_ancestor_tail_or_target H ⟨z, hz⟩ with he | ⟨d, hd⟩
    · change z = H.target at he
      rw [he, htarget]
      exact thinMapBoundaryVertex_mem_sourceAncestorVertices w hfin hL htrans hR P a s
    · have hf : f d.1 ∈ sourceAncestorDarts w hfin hL htrans hR P a s :=
        hdarts ▸ Set.mem_image_of_mem f d.2
      change dartTailVertex H.rep.B.map d.1 = z at hd
      rw [← hd, htail]
      split
      · exact hf.2.2
      · exact hf.2.1
  · intro hv
    rcases ancestorPos_geometric_tail_or_target w hfin hL htrans hR P a s ⟨v, hv⟩ with
      he | ⟨d, hb, hw⟩
    · exact ⟨H.target, Relation.ReflTransGen.refl, htarget.trans he.symm⟩
    · have hm : d.1 ∈ f '' selectedDarts H := hdarts.symm ▸ d.2
      obtain ⟨e, he, hed⟩ := hm
      refine ⟨dartTailVertex H.rep.B.map e, he.1, ?_⟩
      rw [htail, hed, hb]
      exact hw

private theorem ancestorPos_side_reachable {a : ThinMapSide} {u v : ℕ}
    (h : Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a) u v) :
    Reachable (⟨u⟩ : PresentVertex w) ⟨v⟩ := by
  induction h with
  | refl => exact Reachable.rfl
  | tail _ hstep ih =>
      obtain ⟨e, _, hp, hw, he⟩ := hstep
      exact ih.trans ⟨(Hom.toPath ⟨e, hp, hw, he⟩)⟩

include P in
private theorem ancestorPos_boundary_path (a : ThinMapSide) (i d : ℕ) :
    ∃ p : Path (⟨thinMapBoundaryVertex w hfin hL htrans hR a i⟩ : PresentVertex w)
        ⟨thinMapBoundaryVertex w hfin hL htrans hR a (i + d)⟩,
      p.length = d := by
  induction d with
  | zero => exact ⟨.nil, rfl⟩
  | succ d ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨e, _, he, hw, hh⟩ := thinMapBoundaryVertex_step w hfin hL htrans hR P a
        (i + d)
      exact ⟨p.cons ⟨e, he, hw, hh⟩, by rw [Path.length_cons, hp]⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A boundary vertex is an ancestor at level s exactly when its index is at most s.
The reverse inequality is excluded by acyclicity of the actual present-edge graph. -/
theorem ancestorPos_boundary_vertex_mem_iff (a : ThinMapSide) (i s : ℕ) :
    thinMapBoundaryVertex w hfin hL htrans hR a i ∈
      sourceAncestorVertices w hfin hL htrans hR P a s ↔ i ≤ s := by
  constructor
  · intro hi
    by_contra hle
    have hsi : s ≤ i := by omega
    obtain ⟨p, hp⟩ := ancestorPos_boundary_path w hfin hL htrans hR P a s (i - s)
    have hsum : s + (i - s) = i := by omega
    have hreach : Reachable
        (⟨thinMapBoundaryVertex w hfin hL htrans hR a (s + (i - s))⟩ : PresentVertex w)
        ⟨thinMapBoundaryVertex w hfin hL htrans hR a s⟩ := by
      rw [hsum]
      exact ancestorPos_side_reachable w hfin hL htrans hR P hi.2
    obtain ⟨q⟩ := hreach
    have hc := presentVertex_acyclic w _ (p.comp q)
    rw [Path.length_comp, hp] at hc
    omega
  · intro hi
    exact sourceAncestorVertices_mono w hfin hL htrans hR P a hi
      (thinMapBoundaryVertex_mem_sourceAncestorVertices w hfin hL htrans hR P a i)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Exactly the exterior boundary darts with indices strictly below s survive.
This includes the empty level-zero boundary marking. -/
theorem ancestorPos_boundary_dart_mem_iff (a : ThinMapSide) (i s : ℕ) :
    thinMapBoundaryDart w hfin hL htrans hR a i ∈
      sourceAncestorDarts w hfin hL htrans hR P a s ↔ i < s := by
  constructor
  · intro hd
    have hh : thinMapBoundaryVertex w hfin hL htrans hR a (i + 1) ∈
        sourceAncestorVertices w hfin hL htrans hR P a s := hd.2.2
    have hi := (ancestorPos_boundary_vertex_mem_iff w hfin hL htrans hR P a
      (i + 1) s).mp hh
    omega
  · intro hi
    exact sourceAncestorEdges_mono w hfin hL htrans hR P a (by omega : i + 1 ≤ s)
      (thinMapBoundaryDart_mem_sourceAncestorEdges w hfin hL htrans hR P a i)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every finite and geometric ancestor cell is identified by permanent IDs once
the smaller geometric dart-image obligation is discharged. -/
@[expose] noncomputable def ancestorPos_cellEquiv
    (H : HalfTruncationRep) (a : ThinMapSide) (s : ℕ)
    (F : MapVertex H.rep.B.map → ℕ) (f : Fin H.rep.dartCount → ℕ × Bool)
    (hF : Function.Injective F) (hf : Function.Injective f)
    (htail : ∀ d, F (dartTailVertex H.rep.B.map d) =
      if (f d).2 then edgeEast w (f d).1 else edgeWest w (f d).1)
    (htarget : F H.target = thinMapBoundaryVertex w hfin hL htrans hR a s)
    (hdarts : f '' selectedDarts H = sourceAncestorDarts w hfin hL htrans hR P a s) :
    TruncationCell H ≃ SourceAncestorCell w hfin hL htrans hR P a s := by
  have hv := ancestorPos_vertices_image_of_darts w hfin hL htrans hR P
    H a s F f htail htarget hdarts
  let ev := (Equiv.Set.image F (ancestors H) hF).trans
    (Equiv.subtypeEquivRight (fun v => Set.ext_iff.mp hv v))
  let ed := (Equiv.Set.image f (selectedDarts H) hf).trans
    (Equiv.subtypeEquivRight (fun d => Set.ext_iff.mp hdarts d))
  exact Equiv.sumCongr ev ed

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Boundary markings follow from their known finite prefix and the dart-image
identification. All indices, including indices beyond the truncation, are checked. -/
theorem ancestorPos_boundary_mark_iff
    (H : HalfTruncationRep) (a : ThinMapSide) (s : ℕ)
    (ha : H.side = a) (hv : boundaryTarget H.rep.B a s = some H.target)
    (f : Fin H.rep.dartCount → ℕ × Bool) (hf : Function.Injective f)
    (hp : ∀ i < s, ((boundaryDarts H.rep.B a)[i]?).map f =
      some (thinMapBoundaryDart w hfin hL htrans hR a i))
    (hdarts : f '' selectedDarts H = sourceAncestorDarts w hfin hL htrans hR P a s)
    (d : selectedDarts H) (i : ℕ) :
    (boundaryDarts H.rep.B H.side)[i]? = some d.1 ↔
      thinMapBoundaryDart w hfin hL htrans hR a i = f d.1 := by
  subst a
  constructor
  · intro hd
    have hi := (boundary_selectedDart_index_iff H.rep H.side s i H.target d.1 hv hd).mp
      d.2
    have hh := hp i hi
    rw [hd, Option.map_some] at hh
    exact (Option.some.inj hh).symm
  · intro he
    have hm : thinMapBoundaryDart w hfin hL htrans hR H.side i ∈
        sourceAncestorDarts w hfin hL htrans hR P H.side s := by
      rw [he, ← hdarts]
      exact Set.mem_image_of_mem f d.2
    have hi := (ancestorPos_boundary_dart_mem_iff w hfin hL htrans hR P H.side i s).mp hm
    have hh := hp i hi
    rw [he] at hh
    obtain ⟨e, he', hef⟩ := Option.map_eq_some_iff.mp hh
    exact hf hef ▸ he'

end Geometric

section HalfRelations

variable {x : XDP} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ a : ℤ, ∃ n, R w n ≤ a) (P : InfinitePresentPath w ⟨0⟩)
  {ℓ r n m : ℕ} (t : ℕ) (R : KMSWMapRep ℓ r n)
  (hR : xdpLengthBase R.B x = m)
  (J : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide) (s : ℕ) (v : MapVertex (ancestorPosHalfRep R hR a).B.map)

local notation "H" => presentation (ancestorPosHalfRep R hR a) a v
local notation "F" => ancestorPosVertexId w t R hR J a
local notation "f" => ancestorPosDartId w t R hR J a

include J

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Concrete cut halves have a canonical cell equivalence after geometric dart
identification. Vertex identification is derived, rather than added as a premise. -/
@[expose] noncomputable def ancestorPos_halfCellEquiv
    (htarget : F v = thinMapBoundaryVertex w hfin hL htrans hRneg a s)
    (hdarts : f '' selectedDarts H = sourceAncestorDarts w hfin hL htrans hRneg P a s) :
    TruncationCell H ≃ SourceAncestorCell w hfin hL htrans hRneg P a s :=
  ancestorPos_cellEquiv w hfin hL htrans hRneg P H a s F f
    (ancestorPos_ids_injective w t R hR J a).1
    (ancestorPos_ids_injective w t R hR J a).2
    (fun d => (ancestorPos_ids_endpoints w t R hR J a d).1) htarget hdarts

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Permanent IDs preserve every relation except face succession and seam markings.
This is conditional transport only; no geometric identification is asserted. -/
theorem ancestorPos_halfCellEquiv_relations
    (hroot : F (ancestorPosHalfRep R hR a).B.source = 0)
    (htarget : F v = thinMapBoundaryVertex w hfin hL htrans hRneg a s)
    (hv : boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v)
    (hp : ∀ i < s, ((boundaryDarts (ancestorPosHalfRep R hR a).B a)[i]?).map f =
      some (thinMapBoundaryDart w hfin hL htrans hRneg a i))
    (hdarts : f '' selectedDarts H = sourceAncestorDarts w hfin hL htrans hRneg P a s)
    (tag : TruncationRelation) (hface : tag ≠ .faceNext)
    (hseam : ∀ i, tag ≠ .seam i) (u z : TruncationCell H) :
    truncationRelation H tag u z ↔
      sourceAncestorRelation w hfin hL htrans hRneg P a s tag
        (ancestorPos_halfCellEquiv w hfin hL htrans hRneg P t R hR J a s v htarget hdarts u)
        (ancestorPos_halfCellEquiv w hfin hL htrans hRneg P t R hR J a s v htarget hdarts z) := by
  have hF := (ancestorPos_ids_injective w t R hR J a).1
  have hf := (ancestorPos_ids_injective w t R hR J a).2
  cases tag with
  | vertex => cases u <;> cases z <;> rfl
  | root =>
      cases u with
      | inl b =>
          change b.1 = (ancestorPosHalfRep R hR a).B.source ↔ F b.1 = 0
          rw [← hroot]
          exact hF.eq_iff.symm
      | inr d => cases z <;> rfl
  | target =>
      cases u with
      | inl b =>
          change b.1 = v ↔ F b.1 = thinMapBoundaryVertex w hfin hL htrans hRneg a s
          rw [← htarget]
          exact hF.eq_iff.symm
      | inr d => cases z <;> rfl
  | incident =>
      cases u with
      | inl b => cases z <;> rfl
      | inr d =>
          cases z with
          | inl b =>
              change dartTailVertex (ancestorPosHalfRep R hR a).B.map d.1 = b.1 ↔
                (if (f d.1).2 then edgeEast w (f d.1).1 else edgeWest w (f d.1).1) =
                  F b.1
              rw [← (ancestorPos_ids_endpoints w t R hR J a d.1).1]
              exact hF.eq_iff.symm
          | inr e => rfl
  | opposite =>
      cases u with
      | inl b => cases z <;> rfl
      | inr d =>
          cases z with
          | inl b => rfl
          | inr e =>
              change (ancestorPosHalfRep R hR a).B.map.edgeInv d.1 = e.1 ↔
                ((f d.1).1, !(f d.1).2) = f e.1
              rw [← ancestorPos_ids_opposite w t R hR J a d.1]
              exact hf.eq_iff.symm
  | oriented =>
      cases u with
      | inl b => cases z <;> rfl
      | inr d => exact ancestorPos_ids_oriented w t R hR J a d.1
  | rotation =>
      cases u with
      | inl b => cases z <;> rfl
      | inr d =>
          cases z with
          | inl b => rfl
          | inr e =>
              change truncationRelation H .rotation (.inr d) (.inr e) ↔
                ∃ j : ℕ, 0 < j ∧ (kmswInfRot w hfin : _ → _)^[j] (f d.1) = f e.1 ∧
                  ∀ i : ℕ, 0 < i → i < j →
                    (kmswInfRot w hfin : _ → _)^[i] (f d.1) ∉
                      sourceAncestorDarts w hfin hL htrans hRneg P a s
              rw [← hdarts]
              exact ancestorPos_rotation_image w t R hR J a hfin v d e
  | faceNext => exact (hface rfl).elim
  | boundary i =>
      cases u with
      | inl b => cases z <;> rfl
      | inr d =>
          change (boundaryDarts (ancestorPosHalfRep R hR a).B a)[i]? = some d.1 ↔
            thinMapBoundaryDart w hfin hL htrans hRneg a i = f d.1
          exact ancestorPos_boundary_mark_iff w hfin hL htrans hRneg P
            H a s rfl hv f hf hp hdarts d i
  | seam i => exact (hseam i rfl).elim

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The smaller unresolved geometric data: the actual dart image, retained-face
succession and seam indices. Vertex identification, rotation, boundary indices
and the other marked relations are deliberately absent: they are proved above.
This proposition is isolated, not asserted. -/
@[expose] noncomputable def AncestorPosHalfGeometricIdentification : Prop :=
  f '' selectedDarts H = sourceAncestorDarts w hfin hL htrans hRneg P a s ∧
  (∀ d e : selectedDarts H,
    (retainedFace H d.1 ∧
      (ancestorPosHalfRep R hR a).B.map.toCombinatorialMap.faceSucc d.1 = e.1) ↔
    (sourceAncestorRetainedFace w hfin hL htrans hRneg P a s (f d.1) ∧
      kmswInfFaceSucc w hfin (f d.1) = f e.1)) ∧
  (∀ (i : ℕ) (d : selectedDarts H),
    (boundaryDarts (ancestorPosHalfRep R hR a).B (oppositeSide a))[i]? = some d.1 ↔
      (P.edge i, false) = f d.1)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The complete marked isomorphism assembles from the smaller geometric data.
This reduction does not assert that those unresolved data hold. -/
theorem ancestorPos_halfCellEquiv_relation
    (hroot : F (ancestorPosHalfRep R hR a).B.source = 0)
    (htarget : F v = thinMapBoundaryVertex w hfin hL htrans hRneg a s)
    (hv : boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v)
    (hp : ∀ i < s, ((boundaryDarts (ancestorPosHalfRep R hR a).B a)[i]?).map f =
      some (thinMapBoundaryDart w hfin hL htrans hRneg a i))
    (hg : AncestorPosHalfGeometricIdentification w hfin hL htrans hRneg P t R hR J a s v)
    (tag : TruncationRelation) (u z : TruncationCell H) :
    truncationRelation H tag u z ↔
      sourceAncestorRelation w hfin hL htrans hRneg P a s tag
        (ancestorPos_halfCellEquiv w hfin hL htrans hRneg P t R hR J a s v htarget hg.1 u)
        (ancestorPos_halfCellEquiv w hfin hL htrans hRneg P t R hR J a s v htarget hg.1 z) := by
  by_cases hface : tag = .faceNext
  · subst tag
    cases u with
    | inl b => cases z <;> rfl
    | inr d =>
        cases z with
        | inl b => rfl
        | inr e => exact hg.2.1 d e
  · by_cases hseam : ∃ i, tag = .seam i
    · obtain ⟨i, rfl⟩ := hseam
      cases u with
      | inl b => cases z <;> rfl
      | inr d => exact hg.2.2 i d
    · exact ancestorPos_halfCellEquiv_relations w hfin hL htrans hRneg P t R hR J a s v
        hroot htarget hv hp hg.1 tag hface (fun i hi => hseam ⟨i, hi⟩) u z

end HalfRelations

section Reduction

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining positive-cut identification with equivalence construction and eight
relation constructors removed. The root, target and boundary prefix are the known
finite embedding data; the final conjunct isolates the three geometric obligations.
This proposition is neither asserted nor assumed by a completed paper theorem. -/
@[expose] noncomputable def SourceAncestorCutPositiveHalfIdentification : Prop :=
  ∀ (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
    0 < s →
    (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
    let hfin := sourceAncestor_finite_incidence x T hT q
    let hL := sourceAncestor_left_nonneg x T hT q
    let htrans := sourceAncestor_left_transient x T hT q
    let hRneg := sourceAncestor_right_unbounded x T hT q
    let P := sourceAncestorPath x T hT q
    ∃ (ℓ r n m : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
      (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
      selectedCutSide x T a k q.1 =
        some ⟨_, ⟨_, ⟨_, KMSWMapIsoClass.mk (ancestorPosHalfRep R hR a)⟩⟩⟩ ∧
      boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v ∧
      ancestorPosVertexId w t R hR I a (ancestorPosHalfRep R hR a).B.source = 0 ∧
      ancestorPosVertexId w t R hR I a v =
        thinMapBoundaryVertex w hfin hL htrans hRneg a s ∧
      (∀ i < s, ((boundaryDarts (ancestorPosHalfRep R hR a).B a)[i]?).map
        (ancestorPosDartId w t R hR I a) =
          some (thinMapBoundaryDart w hfin hL htrans hRneg a i)) ∧
      AncestorPosHalfGeometricIdentification w hfin hL htrans hRneg P t R hR I a s v

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The smaller half-identification obligation suffices for positive-level realization.
This is a reduction only and does not discharge that obligation. -/
theorem sourceAncestorCutPositiveRealization_of_halfIdentification
    (h : SourceAncestorCutPositiveHalfIdentification x T hT) :
    SourceAncestorCutPositiveRealization x T hT := by
  intro a s k q hs hk
  obtain ⟨ℓ, r, n, m, R, hR, I, v, hrep, hv, hroot, htarget, hp, hg⟩ :=
    h a s k q hs hk
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T (k + 1) q.1).toNat - 1
  let hfin := sourceAncestor_finite_incidence x T hT q
  let hL := sourceAncestor_left_nonneg x T hT q
  let htrans := sourceAncestor_left_transient x T hT q
  let hRneg := sourceAncestor_right_unbounded x T hT q
  let P := sourceAncestorPath x T hT q
  refine ⟨_, _, _, ancestorPosHalfRep R hR a, v, hrep, hv,
    ancestorPos_halfCellEquiv w hfin hL htrans hRneg P t R hR I a s v htarget hg.1, ?_⟩
  exact ancestorPos_halfCellEquiv_relation w hfin hL htrans hRneg P t R hR I a s v
    hroot htarget hv hp hg

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Combining the positive-level reduction with the predecessor's proved level zero -/
theorem sourceAncestorCutRealization_of_halfIdentification
    (h : SourceAncestorCutPositiveHalfIdentification x T hT) :
    SourceAncestorCutRealization x T hT :=
  (sourceAncestorCutRealization_iff_positive x T hT).mpr
    (sourceAncestorCutPositiveRealization_of_halfIdentification x T hT h)

end Reduction
end DirectedDistances.PaperProofs.Section4
