module

public import DirectedDistances.KMSW.StageVertices

/-! # Edges and connectedness of finite KMSW maps

Geometric edges, including missing edges, and connectedness for `def-kmsw`, -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Edge orbits are precisely the allocated geometric edge IDs (`def-kmsw`, -/
@[expose] noncomputable def stageEdgeEquiv (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMap w n).EdgeQuotient ≃ Fin (kmswStage w n).nextEdge := by
  classical
  refine
    { toFun := Quotient.lift Prod.fst ?_
      invFun := fun e => Quotient.mk _ (e, false)
      left_inv := ?_
      right_inv := fun _ => rfl }
  · intro d e h
    rcases (CombinatorialMap.edgeInv_sameCycle_iff (kmswMap w n) d e).1 h with h | h
    · exact congrArg Prod.fst h.symm
    · have hh := congrArg Prod.fst h
      change e.1 = d.1 at hh
      exact hh.symm
  · intro q
    refine Quotient.inductionOn q ?_
    rintro ⟨e, b⟩
    apply Quotient.sound
    apply (CombinatorialMap.edgeInv_sameCycle_iff (kmswMap w n) (e, false) (e, b)).2
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The number of geometric edges equals the number of allocated edge IDs -/
theorem kmswMap_numEdges (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMap w n).numEdges = (kmswStage w n).nextEdge := by
  classical
  unfold CombinatorialMap.numEdges
  simpa only [Fintype.card_fin] using Fintype.card_congr (stageEdgeEquiv w n)

private def VertexStep (s : State) (u v : ℕ) : Prop :=
  ∃ e < s.nextEdge, (s.west e = u ∧ s.east e = v) ∨
    (s.east e = u ∧ s.west e = v)

private theorem vertexStep_symm (s : State) {u v : ℕ} :
    VertexStep s u v → VertexStep s v u := by
  rintro ⟨e, he, h | h⟩
  · exact ⟨e, he, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨e, he, Or.inl ⟨h.2, h.1⟩⟩

private theorem vertexPath_symm (s : State) {u v : ℕ}
    (h : Relation.ReflTransGen (VertexStep s) u v) :
    Relation.ReflTransGen (VertexStep s) v u := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.head (vertexStep_symm s h)

private theorem vertexPath_stable (w : ℕ → Fin 3) (n : ℕ) {u v : ℕ}
    (h : Relation.ReflTransGen (VertexStep (kmswStage w n)) u v) :
    Relation.ReflTransGen (VertexStep (kmswStage w (n + 1))) u v := by
  apply Relation.ReflTransGen.mono (r := VertexStep (kmswStage w n)) ?_ u v h
  intro a b hab
  obtain ⟨e, he, hab⟩ := hab
  have hs := kmswStage_endpoints_stable w (m := n) (n := n + 1) (by omega) he
  exact ⟨e, he.trans_le (kmswStage_nextEdge_mono w (by omega)), by
    simpa only [hs.1, hs.2] using hab⟩

private theorem vertexPath_zero (w : ℕ → Fin 3) (n : ℕ) :
    ∀ v < (kmswStage w n).nextVertex,
      Relation.ReflTransGen (VertexStep (kmswStage w n)) v 0 := by
  induction n with
  | zero =>
    intro v hv
    change v < 2 at hv
    by_cases h : v = 0
    · subst v; exact .refl
    · have h1 : v = 1 := by omega
      subst v
      exact .single ⟨0, by change 0 < 1; decide, Or.inr ⟨rfl, rfl⟩⟩
  | succ n ih =>
    intro v hv
    by_cases ho : v < (kmswStage w n).nextVertex
    · exact vertexPath_stable w n (ih v ho)
    · have ha := act_lt_nextEdge w (m := n) (n := n) (le_refl n)
      have hb := stageEndpoint_lt_nextVertex w n (⟨(kmswStage w n).active, ha⟩, false)
      have ht := stageEndpoint_lt_nextVertex w n (⟨(kmswStage w n).active, ha⟩, true)
      change (kmswStage w n).west (kmswStage w n).active < _ at hb
      change (kmswStage w n).east (kmswStage w n).active < _ at ht
      cases hc : kmswCodeStep (w n) with
      | down =>
        cases hr : (kmswStage w n).UR with
        | nil =>
          have hV : v = (kmswStage w n).nextVertex := by
            simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hr] at hv
            omega
          subst v
          apply Relation.ReflTransGen.head (b := (kmswStage w n).east (kmswStage w n).active)
            ?_ (vertexPath_stable w n (ih _ ht))
          refine ⟨(kmswStage w n).nextEdge, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
            simp [kmswStage, kmswStep, hc, kmswStepOfStep, hr, State.addEdge]
        | cons e es =>
          have hv' : v < (kmswStage w n).nextVertex := by
            simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hr] using hv
          exact (ho hv').elim
      | left =>
        cases hl : (kmswStage w n).UL.dropLast.reverse with
        | nil =>
          have hV : v = (kmswStage w n).nextVertex := by
            simp only [kmswStage, kmswStep, hc, kmswStepOfStep, hl] at hv
            omega
          subst v
          apply Relation.ReflTransGen.head (b := (kmswStage w n).east (kmswStage w n).active)
            ?_ (vertexPath_stable w n (ih _ ht))
          refine ⟨(kmswStage w n).nextEdge, ?_, Or.inl ⟨?_, ?_⟩⟩ <;>
            simp [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge]
        | cons e es =>
          have hv' : v < (kmswStage w n).nextVertex := by
            simpa only [kmswStage, kmswStep, hc, kmswStepOfStep, hl, State.addEdge] using hv
          exact (ho hv').elim
      | up =>
        have hV : v = (kmswStage w n).nextVertex := by
          simp only [kmswStage, kmswStep, hc, kmswStepOfStep] at hv
          omega
        subst v
        apply Relation.ReflTransGen.head (b := (kmswStage w n).west (kmswStage w n).active)
          ?_ (vertexPath_stable w n (ih _ hb))
        refine ⟨(kmswStage w n).nextEdge, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
          simp [kmswStage, kmswStep, hc, kmswStepOfStep, State.addEdge]

private def DartStep (w : ℕ → Fin 3) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge) : Prop :=
  e = (kmswMap w n).rot d ∨ e = (kmswMap w n).rot.symm d ∨
    e = (kmswMap w n).edgeInv d ∨ e = (kmswMap w n).edgeInv.symm d

private theorem rotationPath (w : ℕ → Fin 3) (n : ℕ)
    {d e : StageDart (kmswStage w n).nextEdge}
    (h : stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) e) :
    Relation.ReflTransGen (DartStep w n) d e := by
  obtain ⟨k, rfl⟩ := ((stageRot_sameCycle_iff_endpoint_eq w n d e).2 h).exists_nat_pow_eq
  clear h
  induction k with
  | zero => exact .refl
  | succ k ih =>
    apply ih.tail
    exact Or.inl (by simp only [pow_succ', Equiv.Perm.mul_apply, kmswMap_rot])

private theorem liftVertexPath (w : ℕ → Fin 3) (n : ℕ) {u v : ℕ}
    (h : Relation.ReflTransGen (VertexStep (kmswStage w n)) u v) :
    ∀ d e : StageDart (kmswStage w n).nextEdge,
      stageEndpoint (kmswStage w n) d = u → stageEndpoint (kmswStage w n) e = v →
        Relation.ReflTransGen (DartStep w n) d e := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro d e hd he
    exact rotationPath w n (hd.trans he.symm)
  | @head a b hs _ ih =>
    intro d e hd he
    obtain ⟨f, hf, hs | hs⟩ := hs
    · let x : StageDart (kmswStage w n).nextEdge := (⟨f, hf⟩, false)
      let y : StageDart (kmswStage w n).nextEdge := (⟨f, hf⟩, true)
      have hx : stageEndpoint (kmswStage w n) x = a := hs.1
      have hy : stageEndpoint (kmswStage w n) y = b := hs.2
      have hxy : Relation.ReflTransGen (DartStep w n) x y :=
        .single (Or.inr (Or.inr (Or.inl rfl)))
      exact (rotationPath w n (hd.trans hx.symm)).trans
        (hxy.trans (ih y e hy he))
    · let x : StageDart (kmswStage w n).nextEdge := (⟨f, hf⟩, true)
      let y : StageDart (kmswStage w n).nextEdge := (⟨f, hf⟩, false)
      have hx : stageEndpoint (kmswStage w n) x = a := hs.1
      have hy : stageEndpoint (kmswStage w n) y = b := hs.2
      have hxy : Relation.ReflTransGen (DartStep w n) x y :=
        .single (Or.inr (Or.inr (Or.inl rfl)))
      exact (rotationPath w n (hd.trans hx.symm)).trans
        (hxy.trans (ih y e hy he))

/-- Every finite KMSW map is connected through rotation and geometric edge -/
theorem kmswMap_isConnected (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMap w n).IsConnected := by
  intro d e
  apply liftVertexPath w n
    ((vertexPath_zero w n _ (stageEndpoint_lt_nextVertex w n d)).trans
      (vertexPath_symm _ (vertexPath_zero w n _ (stageEndpoint_lt_nextVertex w n e)))) d e rfl rfl

end DirectedDistances.KMSW
