module

public import DirectedDistances.KMSW.KMSWMapLawFromWalk
public import DirectedDistances.PaperProofs.Section4.ThinMapSideCarrier
import DirectedDistances.PlanarMap.PlanarPathCutHalfMap
public import DirectedDistances.PaperProofs.Section4.FinitePastIndependenceFirstHitKernel

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/


















public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap MeasureTheory

local notation "H" => Option (Σ r : ℕ, KMSW.AllBoltzmannSpace r)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The indexed outer-boundary darts of a finite half. -/
@[expose] def boundaryDarts {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (a : ThinMapSide) : List D :=
  match a with
  | .left => B.leftPath.darts
  | .right => B.rightPath.darts

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The boundary side used for the seam marking. -/
@[expose] def oppositeSide : ThinMapSide → ThinMapSide
  | .left => .right
  | .right => .left

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The source at zero and indexed boundary heads at positive levels. -/
@[expose] def boundaryTarget {D : Type*} [Fintype D] [DecidableEq D]
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (a : ThinMapSide) : ℕ → Option (MapVertex B.map)
  | 0 => some B.source
  | s + 1 => ((boundaryDarts B a)[s]?).map (dartHeadVertex B.map)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An ambient finite half with a side and an ancestor target. -/
structure HalfTruncationRep where
  ℓ : ℕ
  r : ℕ
  n : ℕ
  rep : KMSWMapRep ℓ r n
  side : ThinMapSide
  target : MapVertex rep.B.map

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The vertices that can reach the marked target. -/
@[expose] def ancestors (R : HalfTruncationRep) : Set (MapVertex R.rep.B.map) :=
  {v | Relation.ReflTransGen R.rep.B.map.directedStep v R.target}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
All geometric darts with both endpoints in the ancestor set. -/
@[expose] def selectedDarts (R : HalfTruncationRep) : Set (Fin R.rep.dartCount) :=
  {d | dartTailVertex R.rep.B.map d ∈ ancestors R ∧
    dartHeadVertex R.rep.B.map d ∈ ancestors R}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The disjoint vertex and geometric-dart carrier of the restriction. -/
abbrev TruncationCell (R : HalfTruncationRep) :=
  Sum (ancestors R) (selectedDarts R)

private theorem finite_truncationCells (R : HalfTruncationRep) :
    Finite (TruncationCell R) := by
  classical
  infer_instance

private theorem source_mem_ancestors (R : HalfTruncationRep) :
    R.rep.B.source ∈ ancestors R := by
  classical
  let r := Relation.TransGen R.rep.B.map.directedStep
  let : IsTrans (MapVertex R.rep.B.map) r :=
    ⟨fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂⟩
  let : Std.Irrefl r := ⟨R.rep.B.acyclic⟩
  let : IsStrictOrder (MapVertex R.rep.B.map) r := ⟨⟩
  have hw : WellFounded r :=
    Set.wellFoundedOn_univ.mp (Set.finite_univ.wellFoundedOn (r := r))
  have hall (v : MapVertex R.rep.B.map) :
      Relation.ReflTransGen R.rep.B.map.directedStep R.rep.B.source v := by
    induction v using hw.induction with
    | h v ih =>
        by_cases hp : ∃ u, R.rep.B.map.directedStep u v
        · obtain ⟨u, hu⟩ := hp
          exact Relation.ReflTransGen.tail (ih u (Relation.TransGen.single hu)) hu
        · rw [R.rep.B.source_unique v hp]
  exact hall R.target

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The tags for all incidence, embedding and indexed marking relations. -/
inductive TruncationRelation where
  | vertex
  | root
  | target
  | incident
  | opposite
  | oriented
  | rotation
  | faceNext
  | boundary (i : ℕ)
  | seam (i : ℕ)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The inner faces whose vertices are all ancestors. -/
@[expose] def retainedFace (R : HalfTruncationRep) (d : Fin R.rep.dartCount) :
    Prop :=
  ¬ R.rep.B.map.IsOuter d ∧ ∀ e,
    Equiv.Perm.SameCycle R.rep.B.map.toCombinatorialMap.faceSucc d e →
      dartTailVertex R.rep.B.map e ∈ ancestors R

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The full marked restriction relation used by the existing quotient. -/
@[expose] def truncationRelation (R : HalfTruncationRep) :
    TruncationRelation → TruncationCell R → TruncationCell R → Prop
  | .vertex, .inl _, _ => True
  | .root, .inl v, _ => v.1 = R.rep.B.source
  | .target, .inl v, _ => v.1 = R.target
  | .incident, .inr d, .inl v => dartTailVertex R.rep.B.map d.1 = v.1
  | .opposite, .inr d, .inr e => R.rep.B.map.edgeInv d.1 = e.1
  | .oriented, .inr d, _ => R.rep.B.map.tail d.1
  | .rotation, .inr d, .inr e => ∃ k : ℕ, 0 < k ∧
      (R.rep.B.map.rot : Fin R.rep.dartCount → Fin R.rep.dartCount)^[k] d.1 = e.1 ∧
        ∀ j : ℕ, 0 < j → j < k →
          (R.rep.B.map.rot : Fin R.rep.dartCount → Fin R.rep.dartCount)^[j] d.1 ∉
            selectedDarts R
  | .faceNext, .inr d, .inr e => retainedFace R d.1 ∧
      R.rep.B.map.toCombinatorialMap.faceSucc d.1 = e.1
  | .boundary i, .inr d, _ => (boundaryDarts R.rep.B R.side)[i]? = some d.1
  | .seam i, .inr d, _ =>
      (boundaryDarts R.rep.B (oppositeSide R.side))[i]? = some d.1
  | _, _, _ => False

private def truncationIso (R S : HalfTruncationRep) : Prop :=
  ∃ e : TruncationCell R ≃ TruncationCell S,
    ∀ t x y, truncationRelation R t x y ↔ truncationRelation S t (e x) (e y)

private def truncationSetoid : Setoid HalfTruncationRep where
  r := truncationIso
  iseqv := by
    constructor
    · intro R
      exact ⟨Equiv.refl _, fun _ _ _ => Iff.rfl⟩
    · rintro R S ⟨e, he⟩
      refine ⟨e.symm, fun t x y => ?_⟩
      simpa only [Equiv.apply_symm_apply] using (he t (e.symm x) (e.symm y)).symm
    · rintro R S U ⟨e, he⟩ ⟨f, hf⟩
      exact ⟨e.trans f, fun t x y => (he t x y).trans (hf t (e x) (e y))⟩

private theorem iterate_comm {α β : Type*} (e : α ≃ β) (f : α → α) (g : β → β)
    (h : ∀ x, e (f x) = g (e x)) (k : ℕ) (x : α) :
    e (f^[k] x) = g^[k] (e x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact (ih (f x)).trans (congrArg (g^[k]) (h x))

private theorem reach_iff {α β : Type*} (e : α ≃ β)
    (r : α → α → Prop) (s : β → β → Prop)
    (h : ∀ x y, r x y ↔ s (e x) (e y)) (x y : α) :
    Relation.ReflTransGen r x y ↔ Relation.ReflTransGen s (e x) (e y) := by
  constructor
  · exact Relation.ReflTransGen.lift e (fun _ _ hh => (h _ _).mp hh) x y
  · intro hh
    have hb := Relation.ReflTransGen.lift e.symm (fun u v huv =>
      (h (e.symm u) (e.symm v)).mpr (by simpa only [Equiv.apply_symm_apply] using huv))
        (e x) (e y) hh
    change Relation.ReflTransGen r (e.symm (e x)) (e.symm (e y)) at hb
    simpa only [Equiv.symm_apply_apply] using hb

private theorem step_iff {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) (u v : MapVertex B.map) :
    B.map.directedStep u v ↔ C.map.directedStep (I.vertexEquiv u) (I.vertexEquiv v) := by
  constructor
  · rintro ⟨d, hd, ht, hu, hv⟩
    refine ⟨I.toEquiv d, fun h => hd ((I.missing_iff d).mp h),
      (I.tail_iff d).mpr ht, ?_, ?_⟩
    · exact (I.vertexEquiv_dartTailVertex d).symm.trans (congrArg I.vertexEquiv hu)
    · exact (I.vertexEquiv_dartHeadVertex d).symm.trans (congrArg I.vertexEquiv hv)
  · rintro ⟨d, hd, ht, hu, hv⟩
    let c := I.toEquiv.symm d
    have hc : I.toEquiv c = d := I.toEquiv.apply_symm_apply d
    refine ⟨c, fun h => hd (hc ▸ (I.missing_iff c).mpr h), ?_, ?_, ?_⟩
    · exact (I.tail_iff c).mp (hc.symm ▸ ht)
    · apply I.vertexEquiv.injective
      exact (I.vertexEquiv_dartTailVertex c).trans (hc.symm ▸ hu)
    · apply I.vertexEquiv.injective
      exact (I.vertexEquiv_dartHeadVertex c).trans (hc.symm ▸ hv)

private theorem boundary_map {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) (a : ThinMapSide) :
    (boundaryDarts B a).map I.toEquiv = boundaryDarts C a := by
  cases a with
  | left => exact I.leftDarts
  | right => exact I.rightDarts

private theorem target_map {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) (a : ThinMapSide) (s : ℕ) :
    (boundaryTarget B a s).map I.vertexEquiv = boundaryTarget C a s := by
  cases s with
  | zero => simp only [boundaryTarget, Option.map_some, I.vertexEquiv_source]
  | succ s =>
      simp only [boundaryTarget, ← boundary_map I a, List.getElem?_map, Option.map_map]
      congr 1
      funext d
      exact I.vertexEquiv_dartHeadVertex d

private theorem sameCycle_forward {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : Equiv.Perm α) (g : Equiv.Perm β)
    (h : ∀ x, e (f x) = g (e x)) (x y : α)
    (hh : Equiv.Perm.SameCycle f x y) :
    Equiv.Perm.SameCycle g (e x) (e y) := by
  classical
  obtain ⟨k, hk⟩ := hh.exists_nat_pow_eq
  refine ⟨k, ?_⟩
  have hi := iterate_comm e f g h k x
  rw [perm_iterate_eq_pow f k, perm_iterate_eq_pow g k] at hi
  exact hi.symm.trans (congrArg e hk)

private theorem sameCycle_iff {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : Equiv.Perm α) (g : Equiv.Perm β)
    (h : ∀ x, e (f x) = g (e x)) (x y : α) :
    Equiv.Perm.SameCycle f x y ↔ Equiv.Perm.SameCycle g (e x) (e y) := by
  constructor
  · exact sameCycle_forward e f g h x y
  · intro hh
    have hb := sameCycle_forward e.symm g f (fun z => by
      apply e.injective
      simpa only [Equiv.apply_symm_apply] using (h (e.symm z)).symm)
      (e x) (e y) hh
    simpa only [Equiv.symm_apply_apply] using hb

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The marked presentation attached to a finite representative and target. -/
abbrev presentation {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (a : ThinMapSide)
    (t : MapVertex R.B.map) : HalfTruncationRep := ⟨ℓ, r, n, R, a, t⟩

private theorem presentation_iso {ℓ r n : ℕ} (R S : KMSWMapRep ℓ r n)
    (I : BipolarBoundaryBaseIso R.B S.B) (a : ThinMapSide)
    (t : MapVertex R.B.map) :
    truncationIso (presentation R a t) (presentation S a (I.vertexEquiv t)) := by
  classical
  let P := presentation R a t
  let Q := presentation S a (I.vertexEquiv t)
  have hanc (v : MapVertex R.B.map) :
      v ∈ ancestors P ↔ I.vertexEquiv v ∈ ancestors Q :=
    reach_iff I.vertexEquiv _ _ (step_iff I) v t
  have hdart (d : Fin R.dartCount) :
      d ∈ selectedDarts P ↔ I.toEquiv d ∈ selectedDarts Q := by
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [← I.vertexEquiv_dartTailVertex, ← I.vertexEquiv_dartHeadVertex]
    exact and_congr (hanc _) (hanc _)
  let ev := I.vertexEquiv.subtypeEquiv hanc
  let ed := I.toEquiv.subtypeEquiv hdart
  let e : TruncationCell P ≃ TruncationCell Q := Equiv.sumCongr ev ed
  have hface (d : Fin R.dartCount) : retainedFace P d ↔
      retainedFace Q (I.toEquiv d) := by
    constructor
    · rintro ⟨ho, hf⟩
      refine ⟨fun h => ho ((I.outer_iff d).mp h), ?_⟩
      intro z hz
      let c := I.toEquiv.symm z
      have hc : I.toEquiv c = z := I.toEquiv.apply_symm_apply z
      have hcycle := (sameCycle_iff I.toEquiv _ _ I.faceSucc_comm d c).mpr
        (hc.symm ▸ hz)
      have hh := (hanc _).mp (hf c hcycle)
      rw [I.vertexEquiv_dartTailVertex, hc] at hh
      exact hh
    · rintro ⟨ho, hf⟩
      refine ⟨fun h => ho ((I.outer_iff d).mpr h), ?_⟩
      intro c hc
      have hh := hf (I.toEquiv c)
        ((sameCycle_iff I.toEquiv _ _ I.faceSucc_comm d c).mp hc)
      rw [← I.vertexEquiv_dartTailVertex] at hh
      exact (hanc _).mpr hh
  have hindex (b : ThinMapSide) (i : ℕ) (d : Fin R.dartCount) :
      (boundaryDarts R.B b)[i]? = some d ↔
        (boundaryDarts S.B b)[i]? = some (I.toEquiv d) := by
    rw [← boundary_map I b, List.getElem?_map]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      obtain ⟨c, hc, hcd⟩ := Option.map_eq_some_iff.mp h
      exact I.toEquiv.injective hcd ▸ hc
  have hrot (d f : selectedDarts P) :
      truncationRelation P .rotation (.inr d) (.inr f) ↔
        truncationRelation Q .rotation (.inr (ed d)) (.inr (ed f)) := by
    change (∃ k, 0 < k ∧ _ ∧ _) ↔ (∃ k, 0 < k ∧ _ ∧ _)
    constructor
    · rintro ⟨k, hk, heq, hav⟩
      refine ⟨k, hk, ?_, ?_⟩
      · exact (iterate_comm I.toEquiv _ _ I.rot_comm k d.1).symm.trans
          (congrArg I.toEquiv heq)
      · intro j hj hjk hmem
        apply hav j hj hjk
        apply (hdart _).mpr
        rw [iterate_comm I.toEquiv _ _ I.rot_comm]
        exact hmem
    · rintro ⟨k, hk, heq, hav⟩
      refine ⟨k, hk, ?_, ?_⟩
      · apply I.toEquiv.injective
        exact (iterate_comm I.toEquiv _ _ I.rot_comm k d.1).trans heq
      · intro j hj hjk hmem
        apply hav j hj hjk
        have hh := (hdart _).mp hmem
        rw [iterate_comm I.toEquiv _ _ I.rot_comm] at hh
        exact hh
  refine ⟨e, ?_⟩
  intro tag x y
  cases tag with
  | vertex => cases x <;> cases y <;> rfl
  | root =>
      cases x with
      | inl v =>
          change (v.1 = R.B.source) ↔ (I.vertexEquiv v.1 = S.B.source)
          rw [← I.vertexEquiv_source]
          exact I.vertexEquiv.injective.eq_iff.symm
      | inr d => cases y <;> rfl
  | target =>
      cases x with
      | inl v => exact I.vertexEquiv.injective.eq_iff.symm
      | inr d => cases y <;> rfl
  | incident =>
      cases x with
      | inl v => cases y <;> rfl
      | inr d =>
          cases y with
          | inl v =>
              change (dartTailVertex R.B.map d.1 = v.1) ↔
                (dartTailVertex S.B.map (I.toEquiv d.1) = I.vertexEquiv v.1)
              rw [← I.vertexEquiv_dartTailVertex]
              exact I.vertexEquiv.injective.eq_iff.symm
          | inr f => rfl
  | opposite =>
      cases x with
      | inl v => cases y <;> rfl
      | inr d =>
          cases y with
          | inl v => rfl
          | inr f =>
              change (R.B.map.edgeInv d.1 = f.1) ↔
                (S.B.map.edgeInv (I.toEquiv d.1) = I.toEquiv f.1)
              rw [← I.edgeInv_comm]
              exact I.toEquiv.injective.eq_iff.symm
  | oriented =>
      cases x with
      | inl v => cases y <;> rfl
      | inr d => exact (I.tail_iff d.1).symm
  | rotation =>
      cases x with
      | inl v => cases y <;> rfl
      | inr d =>
          cases y with
          | inl v => rfl
          | inr f => exact hrot d f
  | faceNext =>
      cases x with
      | inl v => cases y <;> rfl
      | inr d =>
          cases y with
          | inl v => rfl
          | inr f =>
              change (retainedFace P d.1 ∧ R.B.map.faceSucc d.1 = f.1) ↔
                (retainedFace Q (I.toEquiv d.1) ∧
                  S.B.map.faceSucc (I.toEquiv d.1) = I.toEquiv f.1)
              rw [← I.faceSucc_comm]
              exact and_congr (hface d.1) I.toEquiv.injective.eq_iff.symm
  | boundary i =>
      cases x with
      | inl v => cases y <;> rfl
      | inr d => exact hindex a i d.1
  | seam i =>
      cases x with
      | inl v => cases y <;> rfl
      | inr d => exact hindex (oppositeSide a) i d.1





def FiniteThinMap := Quotient truncationSetoid





noncomputable def finiteThinMapOfAncestors {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (t : MapVertex R.B.map) : FiniteThinMap :=
  Quotient.mk truncationSetoid (presentation R a t)

private theorem finiteThinMapOfAncestors_eq_iff_aux {ℓ r n ℓ' r' n' : ℕ}
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (a b : ThinMapSide) (v : MapVertex R.B.map) (w : MapVertex S.B.map) :
    finiteThinMapOfAncestors R a v = finiteThinMapOfAncestors S b w ↔
      ∃ e : TruncationCell (presentation R a v) ≃ TruncationCell (presentation S b w),
        ∀ t x y, truncationRelation (presentation R a v) t x y ↔
          truncationRelation (presentation S b w) t (e x) (e y) := by
  change Quotient.mk truncationSetoid _ = Quotient.mk truncationSetoid _ ↔ _
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := truncationSetoid) h

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Equality of restriction classes is exactly an isomorphism of all their marked
relations, even when the ambient halves have different sizes and boundaries. -/
theorem finiteThinMapOfAncestors_eq_iff {ℓ r n ℓ' r' n' : ℕ}
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (a b : ThinMapSide) (v : MapVertex R.B.map) (w : MapVertex S.B.map) :
    finiteThinMapOfAncestors R a v = finiteThinMapOfAncestors S b w ↔
      ∃ e : TruncationCell (presentation R a v) ≃ TruncationCell (presentation S b w),
        ∀ t x y, truncationRelation (presentation R a v) t x y ↔
          truncationRelation (presentation S b w) t (e x) (e y) :=
  finiteThinMapOfAncestors_eq_iff_aux R S a b v w

private theorem source_ancestor_eq {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (v : ancestors (presentation R a R.B.source)) :
    v.1 = R.B.source := by
  rcases Relation.ReflTransGen.cases_tail v.2 with h | ⟨u, _, hu⟩
  · exact h.symm
  · exact (R.B.isSource ⟨u, hu⟩).elim

private theorem source_selectedDarts_empty {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (d : selectedDarts (presentation R a R.B.source)) : False := by
  have ht := source_ancestor_eq R a ⟨_, d.2.1⟩
  have hh := source_ancestor_eq R a ⟨_, d.2.2⟩
  by_cases hd : R.B.map.tail d.1
  · exact R.B.isSource ⟨_, d.1, R.B.noMissingDarts _, hd, rfl, hh⟩
  · have hi : R.B.map.tail (R.B.map.edgeInv d.1) := by
      by_contra h
      exact hd ((R.B.map.tail_iff d.1 (R.B.noMissingDarts _)).mpr h)
    apply R.B.isSource
    refine ⟨_, R.B.map.edgeInv d.1, R.B.noMissingDarts _, hi, rfl, ?_⟩
    simpa only [dartHeadVertex, dartTailVertex, R.B.map.edgeInv_invol] using ht

private def sourceCell {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (a : ThinMapSide) :
    TruncationCell (presentation R a R.B.source) :=
  .inl ⟨R.B.source, Relation.ReflTransGen.refl⟩

private theorem sourceCell_eq {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (z : TruncationCell (presentation R a R.B.source)) :
    z = sourceCell R a := by
  cases z with
  | inl v => exact congrArg Sum.inl (Subtype.ext (source_ancestor_eq R a v))
  | inr d => exact (source_selectedDarts_empty R a d).elim

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At the source every ancestor restriction is the same single marked vertex, across -/
theorem finiteThinMapOfAncestors_source_eq {ℓ r n ℓ' r' n' : ℕ}
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n') (a b : ThinMapSide) :
    finiteThinMapOfAncestors R a R.B.source =
      finiteThinMapOfAncestors S b S.B.source := by
  let e : TruncationCell (presentation R a R.B.source) ≃
      TruncationCell (presentation S b S.B.source) := {
    toFun := fun _ => sourceCell S b
    invFun := fun _ => sourceCell R a
    left_inv := fun z => (sourceCell_eq R a z).symm
    right_inv := fun z => (sourceCell_eq S b z).symm }
  apply (finiteThinMapOfAncestors_eq_iff R S a b R.B.source S.B.source).mpr
  refine ⟨e, ?_⟩
  intro tag x y
  rw [sourceCell_eq R a x, sourceCell_eq R a y]
  cases tag <;> first | rfl | exact iff_of_true rfl rfl

private theorem finiteThinMapOfAncestors_iso_aux {ℓ r n : ℕ}
    (R S : KMSWMapRep ℓ r n) (I : BipolarBoundaryBaseIso R.B S.B)
    (a : ThinMapSide) (t : MapVertex R.B.map) :
    finiteThinMapOfAncestors R a t = finiteThinMapOfAncestors S a (I.vertexEquiv t) :=
  Quotient.sound (presentation_iso R S I a t)



theorem finiteThinMapOfAncestors_iso {ℓ r n : ℕ}
    (R S : KMSWMapRep ℓ r n) (I : BipolarBoundaryBaseIso R.B S.B)
    (a : ThinMapSide) (t : MapVertex R.B.map) :
    finiteThinMapOfAncestors R a t = finiteThinMapOfAncestors S a (I.vertexEquiv t) :=
  finiteThinMapOfAncestors_iso_aux R S I a t



noncomputable instance finiteThinMapMeasurableSpace : MeasurableSpace FiniteThinMap := ⊤



noncomputable instance finiteThinMapOptionMeasurableSpace :
    MeasurableSpace (Option FiniteThinMap) := ⊤

private noncomputable def repTruncate {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (a : ThinMapSide) (s : ℕ) : Option FiniteThinMap :=
  (boundaryTarget R.B a s).map (finiteThinMapOfAncestors R a)

private theorem repTruncate_iso {ℓ r n : ℕ} (R S : KMSWMapRep ℓ r n)
    (I : BipolarBoundaryBaseIso R.B S.B) (a : ThinMapSide) (s : ℕ) :
    repTruncate R a s = repTruncate S a s := by
  unfold repTruncate
  rw [← target_map I a s, Option.map_map]
  apply congrArg (fun f => (boundaryTarget R.B a s).map f)
  funext t
  exact finiteThinMapOfAncestors_iso R S I a t

private noncomputable def classTruncate {ℓ r n : ℕ}
    (a : ThinMapSide) (s : ℕ) : KMSWMapIsoClass ℓ r n → Option FiniteThinMap :=
  KMSWMapIsoClass.lift (fun R => repTruncate R a s) (by
    rintro R S ⟨I⟩
    exact repTruncate_iso R S I a s)





noncomputable def halfTruncate (a : ThinMapSide) (s : ℕ) : H → Option FiniteThinMap
  | none => none
  | some ⟨r, ⟨ℓ, ⟨n, q⟩⟩⟩ => @classTruncate ℓ r n a s q



theorem measurable_cutHalfFunction {α : Type*} [MeasurableSpace α] (f : H → α) :
    Measurable f := by
  exact measurable_of_countable f



theorem measurable_halfTruncate (a : ThinMapSide) (s : ℕ) :
    Measurable (halfTruncate a s) :=
  measurable_cutHalfFunction (halfTruncate a s)

private theorem halfTruncate_none_aux (a : ThinMapSide) (s : ℕ) :
    halfTruncate a s none = none := rfl



theorem halfTruncate_none (a : ThinMapSide) (s : ℕ) :
    halfTruncate a s none = none := halfTruncate_none_aux a s

private theorem halfTruncate_some_mk_aux {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ) :
    halfTruncate a s (some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩) =
      match s with
      | 0 => some (finiteThinMapOfAncestors R a R.B.source)
      | i + 1 =>
          ((match a with
            | .left => R.B.leftPath.darts
            | .right => R.B.rightPath.darts)[i]?).map
              (fun d => finiteThinMapOfAncestors R a (dartHeadVertex R.B.map d)) := by
  cases s with
  | zero => rfl
  | succ i =>
      change ((boundaryDarts R.B a)[i]?.map (dartHeadVertex R.B.map)).map
        (finiteThinMapOfAncestors R a) = _
      rw [Option.map_map]
      rfl




theorem halfTruncate_some_mk {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ) :
    halfTruncate a s (some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩) =
      match s with
      | 0 => some (finiteThinMapOfAncestors R a R.B.source)
      | i + 1 =>
          ((match a with
            | .left => R.B.leftPath.darts
            | .right => R.B.rightPath.darts)[i]?).map
              (fun d => finiteThinMapOfAncestors R a (dartHeadVertex R.B.map d)) :=
  halfTruncate_some_mk_aux R a s

private theorem halfTruncate_some_mk_boundaryTarget_aux {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ) :
    halfTruncate a s (some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩) =
      (boundaryTarget R.B a s).map (finiteThinMapOfAncestors R a) := rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Evaluation on a representative uses its indexed target, including absent targets. -/
theorem halfTruncate_some_mk_boundaryTarget {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (a : ThinMapSide) (s : ℕ) :
    halfTruncate a s (some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩) =
      (boundaryTarget R.B a s).map (finiteThinMapOfAncestors R a) :=
  halfTruncate_some_mk_boundaryTarget_aux R a s

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
An explicit isomorphism of the marked ancestor restrictions gives equality of
truncations at the specified existing targets; the ambient sizes may differ. -/
theorem halfTruncate_some_mk_eq_of_restriction_iso {ℓ r n ℓ' r' n' : ℕ}
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n') (a : ThinMapSide) (s : ℕ)
    (v : MapVertex R.B.map) (w : MapVertex S.B.map)
    (hv : boundaryTarget R.B a s = some v) (hw : boundaryTarget S.B a s = some w)
    (e : TruncationCell (presentation R a v) ≃ TruncationCell (presentation S a w))
    (he : ∀ t x y, truncationRelation (presentation R a v) t x y ↔
      truncationRelation (presentation S a w) t (e x) (e y)) :
    halfTruncate a s (some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩) =
      halfTruncate a s (some ⟨r', ⟨ℓ', ⟨n', KMSWMapIsoClass.mk S⟩⟩⟩) := by
  rw [halfTruncate_some_mk_boundaryTarget, halfTruncate_some_mk_boundaryTarget, hv, hw]
  exact congrArg some ((finiteThinMapOfAncestors_eq_iff R S a a v w).mpr ⟨e, he⟩)

private theorem halfTruncate_isSome_iff_aux {ℓ r n : ℕ} (q : KMSWMapIsoClass ℓ r n)
    (a : ThinMapSide) (s : ℕ) :
    (halfTruncate a s (some ⟨r, ⟨ℓ, ⟨n, q⟩⟩⟩)).isSome = true ↔
      s ≤ (match a with | .left => ℓ | .right => r) := by
  refine KMSWMapIsoClass.ind
    (motive := fun q =>
      (halfTruncate a s (some ⟨r, ⟨ℓ, ⟨n, q⟩⟩⟩)).isSome = true ↔
        s ≤ (match a with | .left => ℓ | .right => r)) ?_ q
  intro R
  rw [halfTruncate_some_mk]
  cases a with
  | left => cases s <;> simp [R.B.leftPath.darts_length]
  | right => cases s <;> simp [R.B.rightPath.darts_length]



theorem halfTruncate_isSome_iff {ℓ r n : ℕ} (q : KMSWMapIsoClass ℓ r n)
    (a : ThinMapSide) (s : ℕ) :
    (halfTruncate a s (some ⟨r, ⟨ℓ, ⟨n, q⟩⟩⟩)).isSome = true ↔
      s ≤ (match a with | .left => ℓ | .right => r) :=
  halfTruncate_isSome_iff_aux q a s

end DirectedDistances.PaperProofs.Section4
