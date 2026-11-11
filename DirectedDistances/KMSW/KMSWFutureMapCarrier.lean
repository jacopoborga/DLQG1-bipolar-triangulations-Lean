module

public import DirectedDistances.KMSW.LimitRotationVertex
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMap
import DirectedDistances.KMSW.StageEdgesConnected
import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.KMSW.StageBoundaryMap

/-! Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty});

The geometric darts include missing edges. Present arrows retain their edge IDs.
These are carrier fields, not a packaged source map or a plane realization.
The initial edge is present, so it cannot serve as a missing frame edge. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Quiver

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
@[expose] def futureMapEdgeInv : Equiv.Perm (ℕ × Bool) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapEdgeInv_invol (d : ℕ × Bool) :
    futureMapEdgeInv (futureMapEdgeInv d) = d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapEdgeInv_ne (d : ℕ × Bool) : futureMapEdgeInv d ≠ d := by
  rcases d with ⟨e, b⟩
  intro h
  have hb : (!b) = b := congrArg Prod.snd h
  cases b <;> cases hb

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
@[expose] def futureMapMissing (w : ℕ → Fin 3) (d : ℕ × Bool) : Prop :=
  ¬ EdgePresent w d.1

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapMissing_edgeInv (w : ℕ → Fin 3) (d : ℕ × Bool) :
    futureMapMissing w d ↔ futureMapMissing w (futureMapEdgeInv d) := Iff.rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
@[expose] def futureMapTail (w : ℕ → Fin 3) (d : ℕ × Bool) : Prop :=
  d.2 = false ∧ EdgePresent w d.1

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapTail_iff (w : ℕ → Fin 3) (d : ℕ × Bool)
    (hp : ¬ futureMapMissing w d) :
    futureMapTail w d ↔ ¬ futureMapTail w (futureMapEdgeInv d) := by
  have he : EdgePresent w d.1 := Classical.not_not.mp hp
  rcases d with ⟨e, b⟩
  cases b <;> simp only [futureMapTail, futureMapEdgeInv, Equiv.coe_fn_mk,
    Bool.not_false, Bool.not_true, Bool.true_eq_false, false_and, not_false_eq_true,
    true_and, he, not_true_eq_false]

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapTail_missing (w : ℕ → Fin 3) (d : ℕ × Bool)
    (hm : futureMapMissing w d) : ¬ futureMapTail w d := fun ht => hm ht.2

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

private theorem futureMapVertex_eq_of_sameCycle (d e : ℕ × Bool)
    (h : (kmswInfRot w hfin).SameCycle d e) :
    kmswLimitDartVertex w d = kmswLimitDartVertex w e := by
  let f := kmswInfRot w hfin
  let g := kmswLimitDartVertex w
  have hf : ∀ x, g (f x) = g x := kmswLimitDartVertex_rot w hfin
  have hi : ∀ x, g (f.symm x) = g x := by
    intro x
    simpa only [Equiv.apply_symm_apply] using (hf (f.symm x)).symm
  obtain ⟨i, he⟩ := h
  have hp : ∀ i : ℤ, g ((f ^ i) d) = g d := by
    intro i
    refine Int.induction_on i ?_ ?_ ?_
    · rfl
    · intro i ih
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply, hf, ih]
    · intro i ih
      have hn : (-(i : ℤ) - 1) = -1 + -(i : ℤ) := by omega
      rw [hn, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      change g (f.symm ((f ^ (-(i : ℤ))) d)) = g d
      rw [hi, ih]
  exact (hp i).symm.trans (congrArg g he)

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Rotation classes are precisely limit vertices. -/
theorem futureMap_sameCycle_iff (d e : ℕ × Bool) :
    (kmswInfRot w hfin).SameCycle d e ↔
      kmswLimitDartVertex w d = kmswLimitDartVertex w e :=
  ⟨futureMapVertex_eq_of_sameCycle w hfin d e,
    kmswLimitDart_same_vertex_sameCycle w hfin d e⟩

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Vertex IDs on the rotation quotient. -/
@[expose] noncomputable def futureMapVertexId :
    RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin) → ℕ :=
  Quotient.lift (kmswLimitDartVertex w)
    (fun d e h => (futureMap_sameCycle_iff w hfin d e).mp h)

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapVertexId_class (d : ℕ × Bool) :
    futureMapVertexId w hfin (rootedLocallyFiniteVertexClass (kmswInfRot w hfin) d) =
      kmswLimitDartVertex w d := rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The west and east classes retain the edge endpoints. -/
theorem futureMapVertexId_endpoints (e : ℕ) :
    futureMapVertexId w hfin
        (rootedLocallyFiniteVertexClass (kmswInfRot w hfin) (e, false)) = edgeWest w e ∧
      futureMapVertexId w hfin
        (rootedLocallyFiniteVertexClass (kmswInfRot w hfin) (e, true)) = edgeEast w e :=
  ⟨rfl, rfl⟩

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. No two distinct limit vertices are collapsed. -/
theorem futureMapVertexId_injective : Function.Injective (futureMapVertexId w hfin) := by
  intro u v
  refine Quotient.inductionOn₂ u v ?_
  intro d e he
  exact Quotient.sound ((futureMap_sameCycle_iff w hfin d e).mpr he)

private theorem futureMapVertex_stage (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    kmswLimitDartVertex w (d.1.val, d.2) = stageEndpoint (kmswStage w n) d := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;>
    simp only [kmswLimitDartVertex, stageEndpoint, hb, Bool.false_eq_true,
      ↓reduceIte, hw, he]

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Finite incidence ensures that every natural vertex ID occurs. -/
theorem futureMapVertexId_surjective : Function.Surjective (futureMapVertexId w hfin) := by
  intro v
  obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence w hfin v
  obtain ⟨d, hd⟩ := stageEndpoint_exists w n v hn
  exact ⟨rootedLocallyFiniteVertexClass (kmswInfRot w hfin) (d.1.val, d.2),
    (futureMapVertex_stage w n d).trans hd⟩

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Each vertex orbit is finite. -/
theorem futureMap_locallyFinite (d : ℕ × Bool) :
    {e : ℕ × Bool | (kmswInfRot w hfin).SameCycle d e}.Finite := by
  apply (kmswLimitDart_star_finite w hfin (kmswLimitDartVertex w d)).subset
  intro e he
  exact ((futureMap_sameCycle_iff w hfin d e).mp he).symm

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Rotation vertices and the present-edge graph have identical vertex IDs. -/
@[expose] noncomputable def futureMapVertexEquiv :
    RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin) ≃ PresentVertex w :=
  Equiv.ofBijective (fun v => ⟨futureMapVertexId w hfin v⟩) ⟨by
    intro u v h
    exact futureMapVertexId_injective w hfin (congrArg PresentVertex.id h), by
    intro v
    obtain ⟨u, hu⟩ := futureMapVertexId_surjective w hfin v.id
    exact ⟨u, congrArg (fun n => (⟨n⟩ : PresentVertex w)) hu⟩⟩

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapVertexEquiv_class (d : ℕ × Bool) :
    futureMapVertexEquiv w hfin
        (rootedLocallyFiniteVertexClass (kmswInfRot w hfin) d) =
      (⟨kmswLimitDartVertex w d⟩ : PresentVertex w) := rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Present tail darts between rotation vertices, retaining geometric edge IDs. -/
@[expose] def FutureMapArrowDart
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) :=
  {d : ℕ × Bool // ¬ futureMapMissing w d ∧ futureMapTail w d ∧
    rootedLocallyFiniteVertexClass (kmswInfRot w hfin) d = u ∧
      rootedLocallyFiniteVertexClass (kmswInfRot w hfin) (futureMapEdgeInv d) = v}

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Parallel arrows are preserved separately, by their original edge IDs. -/
@[expose] noncomputable def futureMapArrowEquiv
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) :
    FutureMapArrowDart w hfin u v ≃
      (futureMapVertexEquiv w hfin u ⟶ futureMapVertexEquiv w hfin v) where
  toFun d := ⟨d.val.1, d.property.2.1.2, by
    change edgeWest w d.val.1 = futureMapVertexId w hfin u
    have hu := congrArg (futureMapVertexId w hfin) d.property.2.2.1
    simpa only [futureMapVertexId_class, kmswLimitDartVertex, d.property.2.1.1,
      Bool.false_eq_true, ↓reduceIte] using hu, by
    change edgeEast w d.val.1 = futureMapVertexId w hfin v
    have hv := congrArg (futureMapVertexId w hfin) d.property.2.2.2
    simpa only [futureMapVertexId_class, futureMapEdgeInv, Equiv.coe_fn_mk,
      kmswLimitDartVertex, d.property.2.1.1, Bool.not_false, ↓reduceIte] using hv⟩
  invFun e := ⟨(e.val, false), (fun hm => hm e.property.1), ⟨rfl, e.property.1⟩, by
    apply futureMapVertexId_injective w hfin
    exact e.property.2.1, by
    apply futureMapVertexId_injective w hfin
    exact e.property.2.2⟩
  left_inv d := Subtype.ext (Prod.ext rfl d.property.2.1.1.symm)
  right_inv _ := Subtype.ext rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The arrow equivalence preserves the actual edge ID. -/
theorem futureMapArrowEquiv_edge
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin))
    (d : FutureMapArrowDart w hfin u v) :
    (futureMapArrowEquiv w hfin u v d).val = d.val.1 := rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Directed steps are exactly nonempty present-arrow dart carriers. -/
theorem futureMap_directedStep_iff
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) :
    rootedLocallyFiniteDirectedStep (kmswInfRot w hfin) futureMapEdgeInv
        (futureMapMissing w) (futureMapTail w) u v ↔
      Nonempty (FutureMapArrowDart w hfin u v) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨⟨d, hd⟩⟩
  · rintro ⟨⟨d, hd⟩⟩
    exact ⟨d, hd⟩

private theorem futureMap_rotation_reach (d e : ℕ × Bool)
    (hv : kmswLimitDartVertex w d = kmswLimitDartVertex w e) :
    Relation.ReflTransGen
      (fun x y : ℕ × Bool => y = kmswInfRot w hfin x ∨
        y = (kmswInfRot w hfin).symm x ∨ y = futureMapEdgeInv x ∨
        y = futureMapEdgeInv.symm x) d e := by
  obtain ⟨k, hk⟩ := (kmswInfRot_exists_pow_iff_endpoint w hfin d e).mpr hv
  rw [← hk]
  clear hk
  induction k with
  | zero => exact .refl
  | succ k ih =>
    exact ih.tail (Or.inl (by rw [pow_succ', Equiv.Perm.mul_apply]))

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. All geometric darts, including missing edges, form a connected map. -/
theorem futureMap_connected (d e : ℕ × Bool) :
    Relation.ReflTransGen
      (fun x y : ℕ × Bool => y = kmswInfRot w hfin x ∨
        y = (kmswInfRot w hfin).symm x ∨ y = futureMapEdgeInv x ∨
        y = futureMapEdgeInv.symm x) d e := by
  let n := max d.1 e.1
  have hd : d.1 < (kmswStage w n).nextEdge :=
    kmsw_nextEdge_unbounded w d.1 n (le_max_left _ _)
  have he : e.1 < (kmswStage w n).nextEdge :=
    kmsw_nextEdge_unbounded w e.1 n (le_max_right _ _)
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  let y : StageDart (kmswStage w n).nextEdge := (⟨e.1, he⟩, e.2)
  let I : StageDart (kmswStage w n).nextEdge → ℕ × Bool := fun z => (z.1.val, z.2)
  let S := fun x y : ℕ × Bool => y = kmswInfRot w hfin x ∨
    y = (kmswInfRot w hfin).symm x ∨ y = futureMapEdgeInv x ∨
    y = futureMapEdgeInv.symm x
  have hstep : ∀ {a b : StageDart (kmswStage w n).nextEdge},
      (b = (kmswMap w n).rot a ∨ b = (kmswMap w n).rot.symm a ∨
        b = (kmswMap w n).edgeInv a ∨ b = (kmswMap w n).edgeInv.symm a) →
      Relation.ReflTransGen S (I a) (I b) := by
    intro a b hab
    rcases hab with hr | hr | hf | hf
    · subst b
      apply futureMap_rotation_reach w hfin
      rw [futureMapVertex_stage, futureMapVertex_stage]
      exact (stageRot_sameCycle_iff_endpoint_eq w n a (stageRot w n a)).mp ⟨1, rfl⟩
    · subst b
      apply futureMap_rotation_reach w hfin
      rw [futureMapVertex_stage, futureMapVertex_stage]
      apply (stageRot_sameCycle_iff_endpoint_eq w n a ((stageRot w n).symm a)).mp
      exact ⟨-1, by simp only [zpow_neg_one, Equiv.Perm.inv_def]⟩
    · subst b
      exact .single (Or.inr (Or.inr (Or.inl rfl)))
    · subst b
      have hinv : (kmswMap w n).edgeInv.symm = (kmswMap w n).edgeInv := by
        apply Equiv.ext
        intro z
        apply (kmswMap w n).edgeInv.injective
        rw [Equiv.apply_symm_apply, (kmswMap w n).edgeInv_invol]
      rw [hinv]
      exact .single (Or.inr (Or.inr (Or.inl rfl)))
  have hlocal := kmswMap_isConnected w n x y
  change Relation.ReflTransGen
    (fun a b : StageDart (kmswStage w n).nextEdge =>
      b = (kmswMap w n).rot a ∨ b = (kmswMap w n).rot.symm a ∨
        b = (kmswMap w n).edgeInv a ∨ b = (kmswMap w n).edgeInv.symm a) x y at hlocal
  have hmap : ∀ {z}, Relation.ReflTransGen
      (fun a b : StageDart (kmswStage w n).nextEdge =>
        b = (kmswMap w n).rot a ∨ b = (kmswMap w n).rot.symm a ∨
          b = (kmswMap w n).edgeInv a ∨ b = (kmswMap w n).edgeInv.symm a) x z →
      Relation.ReflTransGen S (I x) (I z) := by
    intro z hz
    induction hz with
    | refl => exact .refl
    | tail _ h ih => exact ih.trans (hstep h)
  exact hmap hlocal

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. A directed cycle would give a positive closed present-edge path, excluded
by the strict finite-stage ranks used in `presentVertex_acyclic`. -/
theorem futureMap_acyclic :
    ∀ v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin),
      ¬ Relation.TransGen
        (rootedLocallyFiniteDirectedStep (kmswInfRot w hfin) futureMapEdgeInv
          (futureMapMissing w) (futureMapTail w)) v v := by
  have hpath : ∀ {u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)},
      Relation.TransGen
        (rootedLocallyFiniteDirectedStep (kmswInfRot w hfin) futureMapEdgeInv
          (futureMapMissing w) (futureMapTail w)) u v →
      ∃ p : Path (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v),
        0 < p.length := by
    intro u v h
    induction h with
    | single h =>
      obtain ⟨d⟩ := (futureMap_directedStep_iff w hfin _ _).mp h
      exact ⟨(futureMapArrowEquiv w hfin _ _ d).toPath, Nat.zero_lt_one⟩
    | tail _ h ih =>
      obtain ⟨p, _⟩ := ih
      obtain ⟨d⟩ := (futureMap_directedStep_iff w hfin _ _).mp h
      exact ⟨p.cons (futureMapArrowEquiv w hfin _ _ d), Nat.succ_pos _⟩
  intro v hv
  obtain ⟨p, hp⟩ := hpath hv
  rw [presentVertex_acyclic w _ p] at hp
  exact Nat.lt_irrefl 0 hp

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The initial edge is rooted at its west dart. -/
@[expose] def futureMapRootDart : ℕ × Bool := (0, false)

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The candidate frame at the root edge; it is present, not a missing frame. -/
@[expose] def futureMapFrameEdgeDart : ℕ × Bool := futureMapRootDart

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The opposite endpoint mark retains the ordered root edge. -/
@[expose] def futureMapFrameOtherDart : Option (ℕ × Bool) :=
  some (futureMapEdgeInv futureMapFrameEdgeDart)

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMap_root_endpoints :
    kmswLimitDartVertex w futureMapRootDart = 0 ∧
      kmswLimitDartVertex w (futureMapEdgeInv futureMapRootDart) = 1 := ⟨rfl, rfl⟩

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The initial active edge remains present. -/
theorem futureMap_root_present : EdgePresent w futureMapRootDart.1 :=
  ⟨0, by change 0 < 1; decide, rfl⟩

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The exact local topology obstruction: the root edge cannot be the missing frame edge. -/
theorem futureMapFrameEdge_not_missing : ¬ futureMapMissing w futureMapFrameEdgeDart :=
  fun hm => hm (futureMap_root_present w)

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapFrameEdge_at_root :
    (kmswInfRot w hfin).SameCycle futureMapRootDart futureMapFrameEdgeDart :=
  Equiv.Perm.SameCycle.rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a -/
theorem futureMapFrameOtherDart_valid (y : ℕ × Bool)
    (hy : futureMapFrameOtherDart = some y) :
    (kmswInfRot w hfin).SameCycle (futureMapEdgeInv futureMapFrameEdgeDart) y := by
  have he : futureMapEdgeInv futureMapFrameEdgeDart = y := Option.some.inj hy
  rw [← he]

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The face permutation has exactly the rooted-map convention. -/
theorem futureMapFaceSucc_eq :
    kmswInfFaceSucc w hfin = (kmswInfRot w hfin).symm * futureMapEdgeInv := rfl

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The root's east dart marks the persistent lower external boundary. -/
@[expose] def futureMapOuterDart : ℕ × Bool := (0, true)

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. The outer mark is external at every stage. -/
theorem futureMapOuterDart_external : limitExternalDart w futureMapOuterDart := by
  have hLR : ∀ n, 0 ∈ (kmswStage w n).LR := by
    intro n
    induction n with
    | zero => exact List.mem_cons_self
    | succ n ih =>
      obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w n
      rw [ht]
      exact List.mem_append_left _ ih
  refine ⟨0, fun n _ => ?_⟩
  have ha := kmsw_nextEdge_unbounded w 0 n (Nat.zero_le n)
  exact ⟨ha, ((kmswStageDirectedMap_LR_bridge w n ⟨0, ha⟩).mp (hLR n)).2.2⟩

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Right unboundedness removes every missing edge from the UR stack; its
permanent missing status then places it on LL. -/
theorem futureMap_missing_eventually_LL (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (e : ℕ) (hm : ¬ EdgePresent w e) :
    ∃ N, ∀ n, N ≤ n → e < (kmswStage w n).nextEdge ∧ e ∈ (kmswStage w n).LL := by
  obtain ⟨N, hN⟩ := kmswRun_UR_eventually_absent w hR e
  refine ⟨max N e, fun n hn => ?_⟩
  have ha := kmsw_nextEdge_unbounded w e n ((le_max_right _ _).trans hn)
  have hp : (kmswStage w n).present e = false := by
    cases hh : (kmswStage w n).present e with
    | false => rfl
    | true => exact (hm ⟨n, ha, hh⟩).elim
  refine ⟨ha, ?_⟩
  rcases ((kmswStage_status w n).1 e ha).mp hp with hur | hll
  · exact (hN n ((le_max_left _ _).trans hn) hur).elim
  · exact hll

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. A missing edge has its east dart on the persistent external boundary. -/
theorem futureMap_missing_east_external (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (e : ℕ) (hm : ¬ EdgePresent w e) : limitExternalDart w (e, true) := by
  obtain ⟨N, hN⟩ := futureMap_missing_eventually_LL w hR e hm
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨ha, hll⟩ := hN n hn
  exact ⟨ha, ((kmswStageDirectedMap_LL_east w n ⟨e, ha⟩).mpr hll).2⟩

/-- Helper toward Theorem 1.4 / Proposition 5.1 (source future map M_{0,infty}); not a
paper result. Missing edges meet the persistent external boundary on one side.
This does not yet put them in a single limiting face-successor orbit. -/
theorem futureMap_missing_limitExternalDart (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (d : ℕ × Bool) (hm : futureMapMissing w d) :
    limitExternalDart w d ∨ limitExternalDart w (futureMapEdgeInv d) := by
  rcases d with ⟨e, b⟩
  cases b with
  | false => exact Or.inr (futureMap_missing_east_external w hR e hm)
  | true => exact Or.inl (futureMap_missing_east_external w hR e hm)

/- Open record fields for these fixed data:

missing_outer : ∀ d : ℕ × Bool, futureMapMissing w d →
  Equiv.Perm.SameCycle ((kmswInfRot w hfin).symm * futureMapEdgeInv)
      futureMapOuterDart d ∨
    Equiv.Perm.SameCycle ((kmswInfRot w hfin).symm * futureMapEdgeInv)
      futureMapOuterDart (futureMapEdgeInv d)

The persistent external-dart statements above do not prove this single-orbit statement
for a raw walk (even with both L and R unbounded below). The existing
limitExternalDart_iff_sameCycle requires left transience to +infinity and L nonnegative,
which are inappropriate extra assumptions for the raw future map.

frameEdge_missing : futureMapMissing w futureMapFrameEdgeDart

This field is false for the chosen source root edge, by futureMapFrameEdge_not_missing.
This is the local topology carrier gap. No RootedLocallyFiniteMap is packaged here. -/

end DirectedDistances.KMSW
