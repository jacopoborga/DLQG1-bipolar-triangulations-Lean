module

public import DirectedDistances.KMSW.KMSWPeanoPrefixClimb
public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantSteps
public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariant

/-! # First-return corner gaps for a climb

The former `kmswPeanoClimbCorner_vertex_exclusion` and
`kmswPeanoClimbFreshCorner_vertex_exclusion` were removed: they followed from
an all-returns condition and no longer follow from the corrected first-return
corner predicates. First-return gaps may avoid a new dart while sharing its
vertex. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

private theorem firstReturn_avoids_after
    {α β : Type*} (ρ : Equiv.Perm β) (f : α → β)
    (hf : Function.Injective f) (d p : α) (b : β)
    (hd : d ≠ p) (hnext : ρ (f p) = b) (k : ℕ)
    (hfirst : ∀ m : ℕ, 0 < m → m < k →
      (ρ : β → β)^[m] (f d) ∉ Set.range f)
    (m : ℕ) (hm : 0 < m) (hmk : m < k) :
    (ρ : β → β)^[m] (f d) ≠ b := by
  intro hhit
  cases m with
  | zero => omega
  | succ m =>
      have hprev : (ρ : β → β)^[m] (f d) = f p := by
        apply ρ.injective
        rw [← Function.iterate_succ_apply' (f := (ρ : β → β)), hhit, hnext]
      by_cases hm0 : m = 0
      · subst m
        exact hd (hf hprev)
      · exact hfirst m (by omega) (by omega) ⟨p, hprev.symm⟩

private theorem firstReturn_avoids_before
    {α β : Type*} (ρ : Equiv.Perm β) (f : α → β)
    (hf : Function.Injective f) (d y A : α) (b : β)
    (hy : y ≠ A) (hnext : ρ b = f A) (k : ℕ)
    (hret : (ρ : β → β)^[k] (f d) = f y)
    (hfirst : ∀ m : ℕ, 0 < m → m < k →
      (ρ : β → β)^[m] (f d) ∉ Set.range f)
    (m : ℕ) (hm : 0 < m) (hmk : m < k) :
    (ρ : β → β)^[m] (f d) ≠ b := by
  intro hhit
  have hnextHit : (ρ : β → β)^[m + 1] (f d) = f A := by
    rw [Function.iterate_succ_apply', hhit, hnext]
  by_cases hlt : m + 1 < k
  · exact hfirst (m + 1) (by omega) hlt ⟨A, hnextHit.symm⟩
  · have heq : m + 1 = k := by omega
    rw [heq, hret] at hnextHit
    exact hy (hf hnextHit)

-- The reachability argument below includes currently missing geometric edges.
-- It keeps their target orientations separate from the stage's present darts.
private theorem corner_rot_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) (k : ℕ) :
    dartTailVertex B.map ((B.map.toCombinatorialMap.rot : D → D)^[k] d) =
      dartTailVertex B.map d := by
  apply Quotient.sound
  exact (show B.map.toCombinatorialMap.rot.SameCycle d
      ((B.map.toCombinatorialMap.rot : D → D)^[k] d) from
    ⟨(k : ℤ), by simp only [zpow_natCast]; rfl⟩).symm

private theorem corner_image_endpoint
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d e : StageDart (kmswStage (codeExtend c) j).nextEdge)
    (h : stageEndpoint (kmswStage (codeExtend c) j) d =
      stageEndpoint (kmswStage (codeExtend c) j) e) :
    dartTailVertex B.map (P.emb.dartMap d) =
      dartTailVertex B.map (P.emb.dartMap e) := by
  have hrot (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
      dartTailVertex B.map (P.emb.dartMap (stageRot (codeExtend c) j d)) =
        dartTailVertex B.map (P.emb.dartMap d) := by
    obtain ⟨k, _, hk, _⟩ := P.emb.rot_induced d
    change (B.map.toCombinatorialMap.rot : D → D)^[k] (P.emb.dartMap d) =
      P.emb.dartMap (stageRot (codeExtend c) j d) at hk
    rw [← hk]
    exact corner_rot_vertex B _ k
  obtain ⟨k, hk⟩ :=
    ((stageRot_sameCycle_iff_endpoint_eq (codeExtend c) j d e).2 h).exists_nat_pow_eq
  rw [← hk]
  clear hk
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hrot]
      exact ih

private def corner_geoStep (s : State) (x y : ℕ) : Prop :=
  ∃ e < s.nextEdge, s.west e = x ∧ s.east e = y

private theorem corner_geo_stable (u : ℕ → Fin 3) (j : ℕ) {x y : ℕ}
    (h : Relation.ReflTransGen (corner_geoStep (kmswStage u j)) x y) :
    Relation.ReflTransGen (corner_geoStep (kmswStage u (j + 1))) x y := by
  apply Relation.ReflTransGen.mono (r := corner_geoStep (kmswStage u j)) ?_ x y h
  rintro a b ⟨e, he, hw, ht⟩
  have hs := kmswStage_endpoints_stable u (Nat.le_succ j) he
  exact ⟨e, he.trans_le (kmswStage_nextEdge_mono u (Nat.le_succ j)),
    hs.1.trans hw, hs.2.trans ht⟩

private theorem corner_start_stable (s t : State) (es : List ℕ)
    (hwest : ∀ e ∈ es, t.west e = s.west e) :
    boundaryStart t es = boundaryStart s es := by
  cases es with
  | nil => rfl
  | cons e es =>
      change some (t.west e) = some (s.west e)
      rw [hwest e (List.mem_cons_self)]

private theorem corner_geo_source (u : ℕ → Fin 3) (j : ℕ) :
    ∃ v, boundaryStart (kmswStage u j) (kmswStage u j).UL = some v ∧
      ∀ x < (kmswStage u j).nextVertex,
        Relation.ReflTransGen (corner_geoStep (kmswStage u j)) v x := by
  induction j with
  | zero =>
      refine ⟨0, rfl, ?_⟩
      intro x hx
      change x < 2 at hx
      have h : x = 0 ∨ x = 1 := by omega
      rcases h with rfl | rfl
      · exact .refl
      · exact .single ⟨0, by change 0 < 1; decide, rfl, rfl⟩
  | succ j ih =>
      obtain ⟨v, hv, hr⟩ := ih
      let s := kmswStage u j
      let t := kmswStage u (j + 1)
      change boundaryStart s s.UL = some v at hv
      have hULne := (kmswStage_UL_nonempty_active_last u j).1
      have hstart : boundaryStart t s.UL = some v := by
        rw [corner_start_stable s t s.UL]
        · exact hv
        · intro e he
          exact (kmswStage_endpoints_stable u (Nat.le_succ j)
            (stageRotation_UL_bound u j e he)).1
      have hbound := kmswStage_endpoints_lt_nextVertex u j s.active
        (act_lt_nextEdge u (le_refl j))
      have old (x : ℕ) (hx : x < s.nextVertex) :
          Relation.ReflTransGen (corner_geoStep t) v x := corner_geo_stable u j (hr x hx)
      by_cases h0 : u j = 0
      · cases hUL : s.UL.dropLast.reverse with
        | nil =>
            have facts := kmswStage_step_leftFresh_facts u j h0 hUL
            have hE : t.nextEdge = s.nextEdge + 2 := facts.1
            have hV : t.nextVertex = s.nextVertex + 1 := facts.2.1
            have hsingle : s.UL = [s.active] := by
              obtain ⟨xs, hxs⟩ := kmswStage_UL_last u j
              change s.UL = xs ++ [s.active] at hxs
              have hdrop : s.UL.dropLast = [] := List.reverse_eq_nil_iff.mp hUL
              have hx : xs = [] := by
                have hd := congrArg List.dropLast hxs
                simpa only [List.dropLast_append_cons, List.dropLast_singleton,
                  List.append_nil, hdrop] using hd.symm
              simpa only [hx, List.nil_append] using hxs
            have hv' : s.west s.active = v := by
              change boundaryStart s s.UL = some v at hv
              rw [hsingle] at hv
              exact Option.some.inj hv
            refine ⟨s.nextVertex, ?_, ?_⟩
            · change boundaryStart t t.UL = _
              rw [facts.2.2.2.2.2.2.2.2.2.1]
              change some (t.west s.nextEdge) = _
              rw [facts.2.2.1]
            · intro x hx
              have hn : t.nextVertex = s.nextVertex + 1 := facts.2.1
              have hedge : corner_geoStep t s.nextVertex v :=
                ⟨s.nextEdge + 1, by omega,
                  facts.2.2.2.2.1, facts.2.2.2.2.2.1.trans hv'⟩
              by_cases hold : x < s.nextVertex
              · exact (Relation.ReflTransGen.single hedge).trans (old x hold)
              · have heq : x = s.nextVertex := by change x < t.nextVertex at hx; omega
                subst x
                exact .refl
        | cons e es =>
            have facts := kmswStage_step_leftExisting_facts u j e es h0 hUL
            have hV : t.nextVertex = s.nextVertex := facts.2.1
            have hdrop : s.UL.dropLast = es.reverse ++ [e] := by
              have hh := congrArg List.reverse hUL
              simpa only [List.reverse_reverse, List.reverse_cons] using hh
            have hfull : s.UL = es.reverse ++ [e, s.active] := by
              obtain ⟨xs, hxs⟩ := kmswStage_UL_last u j
              change s.UL = xs ++ [s.active] at hxs
              have hxsD : xs = s.UL.dropLast := by rw [hxs]; simp
              rw [hxs, hxsD, hdrop]
              simp only [List.append_assoc, List.singleton_append]
            refine ⟨v, ?_, ?_⟩
            · change boundaryStart t t.UL = some v
              rw [facts.2.2.2.2.2.2.1]
              cases hs : es.reverse with
              | nil =>
                  have hv' : s.west e = v := by
                    rw [hfull, hs] at hv
                    exact Option.some.inj hv
                  change some (t.west s.nextEdge) = _
                  rw [facts.2.2.1, hv']
              | cons f fs =>
                  have hm : f ∈ s.UL := by rw [hfull, hs]; exact List.mem_cons_self
                  have hb := stageRotation_UL_bound u j f hm
                  change some (t.west f) = _
                  rw [(kmswStage_endpoints_stable u (Nat.le_succ j) hb).1]
                  simpa only [hfull, hs, boundaryStart, List.cons_append,
                    List.head?_cons, Option.map_some] using hv
            · intro x hx
              exact old x (by change x < t.nextVertex at hx; omega)
      · by_cases h1 : u j = 1
        · have facts := kmswStage_step_up_facts u j h1
          have hE : t.nextEdge = s.nextEdge + 2 := facts.1
          have hV : t.nextVertex = s.nextVertex + 1 := facts.2.1
          refine ⟨v, ?_, ?_⟩
          · change boundaryStart t t.UL = some v
            rw [facts.2.2.2.2.2.2.2.2.2.1]
            obtain ⟨xs, hxs⟩ := kmswStage_UL_last u j
            change s.UL = xs ++ [s.active] at hxs
            have hdrop : s.UL.dropLast = xs := by rw [hxs]; simp
            rw [hdrop]
            cases xs with
            | nil =>
                have hv' : s.west s.active = v := by
                  rw [hxs] at hv
                  exact Option.some.inj hv
                change some (t.west s.nextEdge) = _
                rw [facts.2.2.1, hv']
            | cons e es =>
                have hm : e ∈ s.UL := by rw [hxs]; exact List.mem_cons_self
                have he := stageRotation_UL_bound u j e hm
                change some (t.west e) = _
                rw [(kmswStage_endpoints_stable u (Nat.le_succ j) he).1]
                simpa only [hxs, boundaryStart, List.cons_append, List.head?_cons,
                  Option.map_some] using hv
          · intro x hx
            by_cases hold : x < s.nextVertex
            · exact old x hold
            · have heq : x = s.nextVertex := by
                change x < t.nextVertex at hx
                omega
              subst x
              exact (old _ hbound.1).tail
                ⟨s.nextEdge, by omega, facts.2.2.1, facts.2.2.2.1⟩
        · have h2 : u j = 2 := by
            have hn0 : (u j).val ≠ 0 := fun h => h0 (Fin.ext h)
            have hn1 : (u j).val ≠ 1 := fun h => h1 (Fin.ext h)
            have hb := (u j).isLt
            apply Fin.ext
            change (u j).val = 2
            omega
          cases hUR : s.UR with
          | cons e es =>
              have facts := kmswStage_step_activation_facts u j e es h2 hUR
              have hV : t.nextVertex = s.nextVertex := facts.2.1
              refine ⟨v, ?_, ?_⟩
              · change boundaryStart t t.UL = some v
                rw [facts.2.2.2.2.2.2.2.1]
                unfold boundaryStart
                rw [List.head?_append_of_ne_nil _ hULne]
                exact hstart
              · intro x hx
                exact old x (by change x < t.nextVertex at hx; omega)
          | nil =>
              have facts := kmswStage_step_pendant_facts u j h2 hUR
              have hE : t.nextEdge = s.nextEdge + 1 := facts.1
              have hV : t.nextVertex = s.nextVertex + 1 := facts.2.1
              refine ⟨v, ?_, ?_⟩
              · change boundaryStart t t.UL = some v
                rw [facts.2.2.2.2.2.2.1]
                unfold boundaryStart
                rw [List.head?_append_of_ne_nil _ hULne]
                exact hstart
              · intro x hx
                by_cases hold : x < s.nextVertex
                · exact old x hold
                · have heq : x = s.nextVertex := by
                    change x < t.nextVertex at hx
                    omega
                  subst x
                  exact (old _ hbound.2).tail
                    ⟨s.nextEdge, by omega, facts.2.2.1, facts.2.2.2.1⟩

private theorem corner_geo_image_reach
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P) {x y : ℕ}
    (h : Relation.ReflTransGen (corner_geoStep (kmswStage (codeExtend c) j)) x y) :
    ∀ d e : StageDart (kmswStage (codeExtend c) j).nextEdge,
      stageEndpoint (kmswStage (codeExtend c) j) d = x →
      stageEndpoint (kmswStage (codeExtend c) j) e = y →
      Relation.ReflTransGen B.map.directedStep
        (dartTailVertex B.map (P.emb.dartMap d))
        (dartTailVertex B.map (P.emb.dartMap e)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro d e hd he
      rw [corner_image_endpoint B c j hj P d e (hd.trans he.symm)]
  | @head x y hs _ ih =>
      intro d e hd he
      obtain ⟨f, hf, hw, ht⟩ := hs
      let p : StageDart (kmswStage (codeExtend c) j).nextEdge := (⟨f, hf⟩, false)
      let q : StageDart (kmswStage (codeExtend c) j).nextEdge := (⟨f, hf⟩, true)
      have hdp := corner_image_endpoint B c j hj P d p (hd.trans hw.symm)
      have hqe := ih q e ht he
      have hflip := P.emb.flip_comm p
      change P.emb.dartMap q = B.map.toCombinatorialMap.edgeInv (P.emb.dartMap p) at hflip
      rw [hflip] at hqe
      rw [hdp]
      exact Relation.ReflTransGen.head
        ⟨P.emb.dartMap p, B.noMissingDarts _, I.geometric_forward f hf, rfl, rfl⟩ hqe

private theorem corner_climb_empty_no_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = []) :
    ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
      dartTailVertex B.map (P.emb.dartMap d) ≠
        dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) := by
  let s := kmswStage (codeExtend c) j
  let a := (kmswRootedStage (codeExtend c) j).root
  have hsingle : s.UL = [s.active] := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last (codeExtend c) j
    change s.UL = xs ++ [s.active] at hxs
    have hdrop : s.UL.dropLast = [] := List.reverse_eq_nil_iff.mp hUL
    have hx : xs = [] := by
      have hd := congrArg List.dropLast hxs
      simpa only [List.dropLast_append_cons, List.dropLast_singleton,
        List.append_nil, hdrop] using hd.symm
    simpa only [hx, List.nil_append] using hxs
  obtain ⟨v, hv, hr⟩ := corner_geo_source (codeExtend c) j
  change boundaryStart s s.UL = some v at hv
  rw [hsingle] at hv
  have hav : stageEndpoint s a = v := Option.some.inj hv
  have hc := peanoStepKind_config B j hj1
  rw [hkind] at hc
  obtain ⟨hs, _, _, _, hparent, hsel, _, _, _⟩ := hc
  let q := B.map.toCombinatorialMap.edgeInv
    (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, hj⟩))
  have hq : B.map.tail q := by
    have hh := (canonicalULSelector B _ hs).property.2.1
    rw [canonicalULSelector_val, ← hsel] at hh
    exact hh
  have hqtail : dartTailVertex B.map q =
      dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) := by
    rw [hparent]
    simp only [ulParent, hs, ↓reduceDIte, canonicalULSelector_val, ← hsel]
    rfl
  have hqhead : dartHeadVertex B.map q =
      dartTailVertex B.map (peanoEdge B ⟨j, hj⟩) := by
    change dartTailVertex B.map
      (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.edgeInv
        (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, hj⟩)))) = _
    rw [B.map.toCombinatorialMap.edgeInv_invol]
    exact corner_rot_vertex B _ 1
  intro d hd
  have hreach := corner_geo_image_reach B c j hj P I
    (hr (stageEndpoint s d) (stageEndpoint_lt_nextVertex (codeExtend c) j d)) a d hav rfl
  rw [P.emb.root_comm, hd] at hreach
  have hstep : B.map.directedStep
      (dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩))
      (dartTailVertex B.map (peanoEdge B ⟨j, hj⟩)) :=
    ⟨q, B.noMissingDarts q, hq, hqtail, hqhead⟩
  exact B.acyclic _ (Relation.TransGen.head' hstep hreach)


/-- The prefix invariant places the two new darts immediately after the
UL predecessor image and immediately before the reversed active image.
First-return minimality therefore excludes them from every unaffected gap. -/
theorem kmswPeanoPrefixInv_climbCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = e :: es) :
    KMSWPeanoClimbCorner B c j hj P hj1
      ((⟨e, (stageRotation_UL_bound (codeExtend c) j) e
        (List.mem_of_mem_dropLast (List.mem_reverse.mp (by
          rw [hUL]
          exact List.mem_cons_self)))⟩, false))
      ((⟨(kmswStage (codeExtend c) j).active,
        act_lt_nextEdge (codeExtend c) (le_refl j)⟩, true)) := by
  let u := codeExtend c
  let s := kmswStage u j
  let a := peanoEdge B ⟨j, hj⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let ρ := B.map.toCombinatorialMap.rot
  have he : e < s.nextEdge := (stageRotation_UL_bound u j) e
    (List.mem_of_mem_dropLast (List.mem_reverse.mp (by
      rw [hUL]
      exact List.mem_cons_self)))
  let p : StageDart s.nextEdge := (⟨e, he⟩, false)
  let A : StageDart s.nextEdge :=
    (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, true)
  have hfront : P.emb.dartMap p = B.map.toCombinatorialMap.edgeInv (ρ a) := by
    obtain ⟨he', _, hmap⟩ :=
      kmswPeanoPrefixInv_climbFrontier_nonempty B c j hj P I hj1 hkind e es hUL
    exact hmap
  have hcfg := peanoStepKind_config B j hj1
  rw [hkind] at hcfg
  obtain ⟨_, _, _, _, _, _, hbconfig, hface, _⟩ := hcfg
  change b = B.map.toCombinatorialMap.edgeInv
    (B.map.toCombinatorialMap.faceSucc a) at hbconfig
  change B.map.toCombinatorialMap.faceSucc (B.map.toCombinatorialMap.faceSucc a) =
    B.map.toCombinatorialMap.edgeInv (ρ a) at hface
  have hrotp : ρ (P.emb.dartMap p) = b := by
    rw [hfront]
    have hprev : ρ.symm b = B.map.toCombinatorialMap.edgeInv (ρ a) := by
      rw [hbconfig]
      exact hface
    exact (congrArg ρ hprev).symm.trans (ρ.apply_symm_apply b)
  have hA : P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv a := by
    have hh := P.emb.flip_comm (kmswRootedStage u j).root
    change P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv
      (P.emb.dartMap (kmswRootedStage u j).root) at hh
    exact hh.trans (congrArg B.map.toCombinatorialMap.edgeInv P.emb.root_comm)
  have hrotz : ρ (B.map.toCombinatorialMap.edgeInv b) = P.emb.dartMap A := by
    rw [hA]
    have hz : B.map.toCombinatorialMap.edgeInv b =
        B.map.toCombinatorialMap.faceSucc a := by
      rw [hbconfig]
      exact B.map.toCombinatorialMap.edgeInv_invol _
    rw [hz]
    exact ρ.apply_symm_apply _
  change KMSWPeanoClimbCorner B c j hj P hj1 p A
  intro d hdp hsucc k _ hret hfirst m hm hmk
  exact ⟨firstReturn_avoids_after ρ P.emb.dartMap P.emb.injective
      d p b hdp hrotp k hfirst m hm hmk,
    firstReturn_avoids_before ρ P.emb.dartMap P.emb.injective
      d (stageRot u j d) A (B.map.toCombinatorialMap.edgeInv b)
      hsucc hrotz k hret hfirst m hm hmk⟩

/-- With no UL predecessor, geometric reachability and target acyclicity
exclude every old image dart from the new tail vertex. At the two old
vertices, the new darts lie just after the active dart and just before its
reverse. These facts prove the fresh first-return corner without a separate
freshness hypothesis. -/
theorem kmswPeanoPrefixInv_climbFreshCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (I : KMSWPeanoPrefixInv B c j hj P)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = []) :
    KMSWPeanoClimbFreshCorner B c j hj P hj1
      ((⟨(kmswStage (codeExtend c) j).active,
        act_lt_nextEdge (codeExtend c) (le_refl j)⟩, false))
      ((⟨(kmswStage (codeExtend c) j).active,
        act_lt_nextEdge (codeExtend c) (le_refl j)⟩, true)) := by
  let u := codeExtend c
  let s := kmswStage u j
  let a := peanoEdge B ⟨j, hj⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let ρ := B.map.toCombinatorialMap.rot
  let p : StageDart s.nextEdge :=
    (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, false)
  let A : StageDart s.nextEdge :=
    (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, true)
  have hp : P.emb.dartMap p = a := P.emb.root_comm
  have hA : P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv a := by
    have hh := P.emb.flip_comm p
    change P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv (P.emb.dartMap p) at hh
    exact hh.trans (congrArg B.map.toCombinatorialMap.edgeInv hp)
  have hcfg := peanoStepKind_config B j hj1
  rw [hkind] at hcfg
  obtain ⟨_, _, _, _, _, _, hbconfig, _, _⟩ := hcfg
  change b = B.map.toCombinatorialMap.edgeInv
    (B.map.toCombinatorialMap.faceSucc a) at hbconfig
  have hrotz : ρ (B.map.toCombinatorialMap.edgeInv b) = P.emb.dartMap A := by
    rw [hA]
    have hz : B.map.toCombinatorialMap.edgeInv b =
        B.map.toCombinatorialMap.faceSucc a := by
      rw [hbconfig]
      exact B.map.toCombinatorialMap.edgeInv_invol _
    rw [hz]
    exact ρ.apply_symm_apply _
  have hvertex := corner_climb_empty_no_vertex B c j hj P I hj1 hkind hUL
  have avoids (d : StageDart s.nextEdge) (m : ℕ) (q : D)
      (hq : dartTailVertex B.map q = dartTailVertex B.map b) :
      (ρ : D → D)^[m] (P.emb.dartMap d) ≠ q := by
    intro hhit
    exact hvertex d ((corner_rot_vertex B (P.emb.dartMap d) m).symm.trans
      ((congrArg (dartTailVertex B.map) hhit).trans hq))
  change KMSWPeanoClimbFreshCorner B c j hj P hj1 p A
  intro d hdp hsucc k _ hret hfirst m hm hmk
  refine ⟨avoids d m b rfl, ?_, ?_, ?_⟩
  · exact firstReturn_avoids_before ρ P.emb.dartMap P.emb.injective
      d (stageRot u j d) A (B.map.toCombinatorialMap.edgeInv b)
      hsucc hrotz k hret hfirst m hm hmk
  · exact firstReturn_avoids_after ρ P.emb.dartMap P.emb.injective
      d p (ρ a) hdp (congrArg ρ hp) k hfirst m hm hmk
  · exact avoids d m (B.map.toCombinatorialMap.edgeInv (ρ a))
      (peanoClimb_edgeInv_rot_tail_eq_next B j hj1 hkind)

end DirectedDistances.KMSW
