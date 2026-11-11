/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart7
public import DirectedDistances.PaperProofs.Section3.IntrinsicDirectedDistance
public import DirectedDistances.PaperProofs.Section3.UIBOTLawStatementsSections135













public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open MeasureTheory ProbabilityTheory Filter

/-- Helper toward Proposition 3.9: the complete Lemma 3.10 statement in
representative coordinates. Rays and missing flags are KMSW-defined; the
ambient vertices and individual edges are carried through the start isomorphism
and the supplied ambient equivalences. All integer starts share this predicate. -/
@[expose] def IntrinsicConsumerBoundary (W : ℤ → Fin 3)
    (A : D39DomainRootedMap.{0}) (V₀ : WholePlaneVertex W ≃ A.V)
    (E₀ : WholePlaneEdge W ≃ A.E) : Prop :=
  ∀ n : ℤ, ∃ J : WholePlaneStartIso W n,
    let U := shiftWordInt W n
    let V := J.vertex.trans V₀
    let E := J.edge.trans E₀
    ∃ (H : WholePlaneRotationHypothesis U)
      (_h : BoundaryHitWitnesses (shiftedStream U 0)),
      let w := shiftedStream U 0
      let incl := wholePlaneEdgeι U 0
      let lam := m0CutLambdaZero U
      ∃ (P : WholePlaneRightmostRay U H)
        (Q : M0CutLeftmostChain U H (wholePlaneEdgeWest U lam)),
        E lam = E (incl 0) ∧
        V (P.vertex 0) = V (wholePlaneEdgeEast U lam) ∧
        (∀ P' : WholePlaneRightmostRay U H,
          V (P'.vertex 0) = V (wholePlaneEdgeEast U lam) →
            V ∘ P'.vertex = V ∘ P.vertex ∧ E ∘ P'.edge = E ∘ P.edge) ∧
        (∀ Q' : M0CutLeftmostChain U H (wholePlaneEdgeWest U lam),
          V ∘ Q'.vertex = V ∘ Q.vertex ∧ E ∘ Q'.edge = E ∘ Q.edge) ∧
        (E ∘ incl) '' kmswRunBoundaryEdges w =
          {E lam} ∪ Set.range (E ∘ P.edge) ∪ Set.range (E ∘ Q.edge) ∧
        (∀ v : ℕ, RunBoundaryVertex w v ↔
          V (wholePlaneVertexι U 0 v) ∈ Set.range (V ∘ P.vertex) ∪ Set.range (V ∘ Q.vertex)) ∧
        EdgePresent w 0 ∧
        (∀ e ∈ kmswRunBoundaryEdges w,
          (E (incl e) ∈ ({E lam} ∪ Set.range (E ∘ P.edge)) → EdgePresent w e) ∧
          (E (incl e) ∈ Set.range (E ∘ Q.edge) → ¬ EdgePresent w e)) ∧
        (∀ j : ℕ, wholePlaneEdgePresent U (Q.edge j) ∧
          wholePlaneLeftmostIncomingAt U H (Q.vertex j) (Q.edge j) ∧
          V (wholePlaneEdgeEast U (Q.edge j)) = V (Q.vertex j)) ∧
        (∀ j : ℕ, V (wholePlaneEdgeWest U (Q.edge j)) = V (Q.vertex (j + 1))) ∧
        (∀ v : ℕ,
          (∃ e, EdgePresent w e ∧ V (wholePlaneVertexι U 0 (edgeWest w e)) =
            V (wholePlaneVertexι U 0 v)) ∧
          ((∃ e, EdgePresent w e ∧ V (wholePlaneVertexι U 0 (edgeEast w e)) =
            V (wholePlaneVertexι U 0 v)) ↔
            V (wholePlaneVertexι U 0 v) ∉ Set.range (V ∘ Q.vertex))) ∧
        (∀ v : ℕ, ∃ R : KMSWRunRightmostRay w (H.1 0),
          V (wholePlaneVertexι U 0 (R.vertex 0)) = V (wholePlaneVertexι U 0 v)) ∧
        (∀ R R' : KMSWRunRightmostRay w (H.1 0),
          V (wholePlaneVertexι U 0 (R.vertex 0)) = V (wholePlaneVertexι U 0 (R'.vertex 0)) →
            (fun i => V (wholePlaneVertexι U 0 (R.vertex i))) =
              (fun i => V (wholePlaneVertexι U 0 (R'.vertex i))) ∧
            (fun i => E (incl (R.edge i))) = (fun i => E (incl (R'.edge i)))) ∧
        (∀ R : KMSWRunRightmostRay w (H.1 0),
          V (wholePlaneVertexι U 0 (R.vertex 0)) = V (P.vertex 0) →
            ∀ i, V (wholePlaneVertexι U 0 (R.vertex i)) = V (P.vertex i) ∧
              E (incl (R.edge i)) = E (P.edge i)) ∧
        (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
          ∀ R R' : KMSWRunRightmostRay w (H.1 0),
            R.vertex 0 = x → R'.vertex 0 = x' →
              ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                V (wholePlaneVertexι U 0 (R.vertex (s + t))) =
                  V (wholePlaneVertexι U 0 (R'.vertex (s' + t))) ∧
                E (incl (R.edge (s + t))) = E (incl (R'.edge (s' + t)))) ∧
        (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
          ∀ e e' : ℕ, EdgePresent w e → EdgePresent w e' →
            edgeWest w e = x → edgeWest w e' = x' →
            ∀ R R' : KMSWRunRightmostRay w (H.1 0),
              R.vertex 0 = edgeEast w e → R'.vertex 0 = edgeEast w e' →
                ∃ s s' : ℕ, 1 ≤ s ∧ 1 ≤ s' ∧ ∀ t : ℕ,
                  V (wholePlaneVertexι U 0 (R.vertex (s - 1 + t))) =
                    V (wholePlaneVertexι U 0 (R'.vertex (s' - 1 + t))) ∧
                  E (incl (R.edge (s - 1 + t))) = E (incl (R'.edge (s' - 1 + t)))) ∧
        (∀ x : ℕ, RunBoundaryVertex w x →
          ∃ P1 : WholePlaneRightmostRay U H,
            V (P1.vertex 0) = V (wholePlaneVertexι U 0 x)) ∧
        (∀ x x' : ℕ, RunBoundaryVertex w x → RunBoundaryVertex w x' →
          ∀ P1 P2 : WholePlaneRightmostRay U H,
            V (P1.vertex 0) = V (wholePlaneVertexι U 0 x) →
            V (P2.vertex 0) = V (wholePlaneVertexι U 0 x') →
              ∃ s s' : ℕ, 0 < s ∧ 0 < s' ∧ ∀ t : ℕ,
                V (P1.vertex (s + t)) = V (P2.vertex (s' + t)))

/-- Helper toward Proposition 3.9: Lemma 3.10 transports simultaneously
through every ambient vertex and edge equivalence, retaining its complete
KMSW characterization and every integer-start isomorphism. -/
theorem intrinsicConsumers38_sample :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (A : D39DomainRootedMap.{0}) (V₀ : WholePlaneVertex W ≃ A.V)
        (E₀ : WholePlaneEdge W ≃ A.E), IntrinsicConsumerBoundary W A V₀ E₀ := by
  filter_upwards [DirectedDistances.Paper.Section3.lem_uibot_bdy] with W hW
  intro A V₀ E₀ n
  obtain ⟨hb, ⟨J⟩⟩ := hW n
  dsimp only at hb
  obtain ⟨H, h, P, Q, hlam, hp0, hpu, hqu, hbd, hbv, hr0,
    hmissing, hqin, hqout, hinc, hex, hun, hagree, hcoal, hfirst, haex, hacoal⟩ := hb
  let V := J.vertex.trans V₀
  let E := J.edge.trans E₀
  have hv (a b : ℕ) : V (wholePlaneVertexι (shiftWordInt W n) 0 a) =
      V (wholePlaneVertexι (shiftWordInt W n) 0 b) ↔ a = b :=
    V.injective.eq_iff.trans (wholePlaneVertexι_injective _ 0).eq_iff
  have hvr (v : WholePlaneVertex (shiftWordInt W n)) (f : ℕ → WholePlaneVertex (shiftWordInt W n)) :
      V v ∈ Set.range (V ∘ f) ↔ v ∈ Set.range f := by
    simp only [Set.mem_range, Function.comp_apply, V.injective.eq_iff]
  have her (e : WholePlaneEdge (shiftWordInt W n)) (f : ℕ → WholePlaneEdge (shiftWordInt W n)) :
      E e ∈ Set.range (E ∘ f) ↔ e ∈ Set.range f := by
    simp only [Set.mem_range, Function.comp_apply, E.injective.eq_iff]
  dsimp only [V, E] at hv hvr her
  refine ⟨J, H, h, P, Q, congrArg E hlam, congrArg V hp0, ?_, ?_, ?_, ?_, hr0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P' hp'
    obtain ⟨h1, h2⟩ := hpu P' (V.injective hp')
    exact ⟨congrArg (fun f => V ∘ f) h1, congrArg (fun f => E ∘ f) h2⟩
  · intro Q'
    obtain ⟨h1, h2⟩ := hqu Q'
    exact ⟨congrArg (fun f => V ∘ f) h1, congrArg (fun f => E ∘ f) h2⟩
  · have hs := congrArg (fun s => E '' s) hbd
    simpa only [E, Set.image_union, Set.image_singleton, ← Set.range_comp,
      Set.image_image, Function.comp_def] using hs
  · intro v
    simpa only [Set.mem_union, hvr] using hbv v
  · intro e he
    simpa only [Set.mem_union, Set.mem_singleton_iff, (J.edge.trans E₀).injective.eq_iff, her]
      using hmissing e he
  · intro j
    exact ⟨(hqin j).1, (hqin j).2.1, congrArg V (hqin j).2.2⟩
  · intro j
    exact congrArg V (hqout j)
  · intro v
    simpa only [hv, hvr] using hinc v
  · intro v
    obtain ⟨R, hR⟩ := hex v
    exact ⟨R, congrArg (fun a => V (wholePlaneVertexι _ 0 a)) hR⟩
  · intro R R' heq
    obtain ⟨h1, h2⟩ := hun R R' ((hv _ _).mp heq)
    exact ⟨congrArg (fun f i => V (wholePlaneVertexι _ 0 (f i))) h1,
      congrArg (fun f i => E (wholePlaneEdgeι _ 0 (f i))) h2⟩
  · intro R hR i
    obtain ⟨h1, h2⟩ := hagree R (V.injective hR) i
    exact ⟨congrArg V h1, congrArg E h2⟩
  · intro x x' hx hx' R R' hR hR'
    obtain ⟨s, s', hs, hs', ht⟩ := hcoal x x' hx hx' R R' hR hR'
    exact ⟨s, s', hs, hs', fun t =>
      ⟨congrArg (fun a => V (wholePlaneVertexι _ 0 a)) (ht t).1,
       congrArg (fun e => E (wholePlaneEdgeι _ 0 e)) (ht t).2⟩⟩
  · intro x x' hx hx' e e' he he' hx0 hx0' R R' hR hR'
    obtain ⟨s, s', hs, hs', ht⟩ := hfirst x x' hx hx' e e' he he' hx0 hx0' R R' hR hR'
    exact ⟨s, s', hs, hs', fun t =>
      ⟨congrArg (fun a => V (wholePlaneVertexι _ 0 a)) (ht t).1,
       congrArg (fun e => E (wholePlaneEdgeι _ 0 e)) (ht t).2⟩⟩
  · intro x hx
    obtain ⟨P1, hP1⟩ := haex x hx
    exact ⟨P1, congrArg V hP1⟩
  · intro x x' hx hx' P1 P2 h1 h2
    obtain ⟨s, s', hs, hs', ht⟩ := hacoal x x' hx hx' P1 P2 (V.injective h1) (V.injective h2)
    exact ⟨s, s', hs, hs', fun t => congrArg V (ht t)⟩

/-- Helper toward Proposition 3.9: both complete rooted-map certificates
of Proposition 5.1, together with the transported geometric edge carriers,
vertex incidence, dart maps and retained missing primed root. The certificates
retain rotation, faces and exterior incidence in their KMSW coordinates. -/
@[expose] def IntrinsicConsumerFutureMaps (W : ℤ → Fin 3)
    (A : D39DomainRootedMap.{0}) (V₀ : WholePlaneVertex W ≃ A.V)
    (E₀ : WholePlaneEdge W ≃ A.E) (K₀ : WholePlaneDart W ≃ (A.E × Bool)) : Prop :=
  ∀ n : ℤ, ∃ J : WholePlaneStartIso W n,
    let U := shiftWordInt W n
    let V := fun v => V₀ (J.vertex (wholePlaneVertexι U 0 v))
    let E := fun e => E₀ (J.edge (wholePlaneEdgeι U 0 e))
    let K := fun d => K₀ (J.dart (wholePlaneDartι U 0 d))
    let u := fun i => futureMapShiftedCodePath n W (i + 1)
    u = shiftedStream U 0 ∧
      ∃ (h : HasFlowLineHits u) (hh : hatLimitFiniteIncidence u)
        (hp : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
        hatLawCodes (futureMapShiftedCodePath n W) = hatCodes u h ∧
        hatLawPrimedCodes (futureMapShiftedCodePath n W) = primedCode (primedSimInput u) h ∧
        hatRootedMapClause u h hh ∧ primedRootedMapClause u h hp hb ∧
        Function.Injective (E ∘ hatLimitEdgeMap u h) ∧
        Function.Injective (E ∘ primedLimitEdgeMap u h) ∧
        Set.range (E ∘ hatLimitEdgeMap u h) =
          E '' {e | EdgePresent u e ∧ MhatGeometricEdge u e} ∧
        Set.range (E ∘ primedLimitEdgeMap u h) = E '' {e | primeGeomEdge u hp hb e} ∧
        (∀ e, V (edgeWest u (hatLimitEdgeMap u h e)) =
            V (hatLimitVertexMap u h (edgeWest (hatCodes u h) e)) ∧
          V (edgeEast u (hatLimitEdgeMap u h e)) =
            V (hatLimitVertexMap u h (edgeEast (hatCodes u h) e))) ∧
        E (primedLimitEdgeMap u h 0) = E (kmswLLCreatedEdge u (walkNL u h 0)) ∧
        ¬ PrimedEdgePresent u h 0 ∧
        (∀ d, K (primedLimitDartMap u h (futureMapEdgeInv d)) =
          K (futureMapEdgeInv (primedLimitDartMap u h d))) ∧
        Function.Injective (fun d : ℕ × Bool => K (hatLimitEdgeMap u h d.1, d.2)) ∧
        Function.Injective (K ∘ primedLimitDartMap u h)

/-- Helper toward Proposition 3.9: the generating-code independence and
UIQBOT law in Proposition 5.1. These are law statements and therefore sit
outside the pointwise conull-event certificates. -/
theorem intrinsicConsumers51_generating_laws :
    (∀ n : ℤ, (hatLawCodes ∘ futureMapShiftedCodePath n) ⟂ᵢ[wholePlaneIIDCodeMeasure]
      (hatLawPrimedCodes ∘ futureMapShiftedCodePath n)) ∧
    (∀ n : ℤ, wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
      iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1)))) :=
  ⟨DirectedDistances.Paper.Section5.future_map_law.1,
    DirectedDistances.Paper.Section5.future_map_law.2.1⟩

/-- Helper toward Proposition 3.9: the complete KMSW rooted-map
certificates and their explicit representative coordinates hold at every
integer shift on one iid event, for every supplied ambient equivalence. -/
theorem intrinsicConsumers51_sample :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (A : D39DomainRootedMap.{0}) (V₀ : WholePlaneVertex W ≃ A.V)
        (E₀ : WholePlaneEdge W ≃ A.E) (K₀ : WholePlaneDart W ≃ (A.E × Bool)),
        IntrinsicConsumerFutureMaps W A V₀ E₀ K₀ := by
  filter_upwards [DirectedDistances.Paper.Section3.lem_uibot_bdy,
    DirectedDistances.Paper.Section5.future_map_law.2.2] with W hbd hW
  intro A V₀ E₀ K₀ n
  obtain ⟨_, ⟨J⟩⟩ := hbd n
  obtain ⟨hu, h, hh, hp, hb, hhat, hprime, hmaps⟩ := hW n
  let U := shiftWordInt W n
  let u := fun i => futureMapShiftedCodePath n W (i + 1)
  let V := fun v => V₀ (J.vertex (wholePlaneVertexι U 0 v))
  let E := fun e => E₀ (J.edge (wholePlaneEdgeι U 0 e))
  let K := fun d => K₀ (J.dart (wholePlaneDartι U 0 d))
  have hE : Function.Injective E :=
    E₀.injective.comp (J.edge.injective.comp (wholePlaneEdgeι_injective U 0))
  have hK : Function.Injective K := by
    intro a b heq
    have h := J.dart.injective (K₀.injective heq)
    change (wholePlaneEdgeι U 0 a.1, a.2) = (wholePlaneEdgeι U 0 b.1, b.2) at h
    apply Prod.ext
    · exact wholePlaneEdgeι_injective U 0 (congrArg Prod.fst h)
    · have hs := congrArg (fun d : WholePlaneEdge U × Bool => d.2) h
      exact hs
  have hhatRange : Set.range (hatLimitEdgeMap u h) =
      {e | EdgePresent u e ∧ MhatGeometricEdge u e} := by
    ext e
    exact hatLimitEdgeMap_range_iff u h e
  have hprimeRange : Set.range (primedLimitEdgeMap u h) = {e | primeGeomEdge u hp hb e} := by
    ext e
    exact (primeGeomEdge_iff_primedLimitEdge u hp hb h e).symm
  obtain ⟨Hhat, Fhat, hHhat, hroot, hinv, hmissing, htail, hends, hrest⟩ := hmaps.1
  have hhatClause : hatRootedMapClause u h hh := hmaps.1
  have hprimeClause : primedRootedMapClause u h hp hb := hmaps.2
  obtain ⟨Hprime, Vprime, Fprime, hHprime, hvprime, hrootprime,
    hmissingprime, hprimezero, hrestprime⟩ := hprimeClause
  refine ⟨J, hu, h, hh, hp, hb, hhat, hprime, hhatClause, hmaps.2,
    hE.comp (hatLimitEdgeMap_injective u h), hE.comp (primedLimitEdgeMap_injective u h),
    ?_, ?_, ?_, congrArg E (primedLimitEdgeMap_zero u h), hprimezero, ?_, ?_,
    hK.comp (primedLimitDartMap_injective u h)⟩
  · change Set.range (E ∘ hatLimitEdgeMap u h) = _
    rw [Set.range_comp, hhatRange]
  · change Set.range (E ∘ primedLimitEdgeMap u h) = _
    rw [Set.range_comp, hprimeRange]
  · intro e
    exact ⟨congrArg V (hends e).1, congrArg V (hends e).2⟩
  · intro d
    exact congrArg K (primedLimitDartMap_edgeInv u h d)
  · apply hK.comp
    intro a b heq
    change (hatLimitEdgeMap u h a.1, a.2) = (hatLimitEdgeMap u h b.1, b.2) at heq
    apply Prod.ext
    · exact hatLimitEdgeMap_injective u h (congrArg Prod.fst heq)
    · have hs := congrArg (fun d : ℕ × Bool => d.2) heq
      exact hs

/-- Helper toward Proposition 3.9: every s41 edge-list path has a finite
vertex enumeration with length-one intrinsic paths at successive vertices.
Every enumerated vertex is the initial vertex or the head of a listed edge. -/
theorem intrinsicConsumerPath_vertices (A : D39DomainRootedMap.{0})
    (S : Set A.E) (missing : A.E → Prop) {u v : A.V} {es : List A.E}
    (p : IntrinsicDirectedEdgeListPath A S missing u v es) :
    ∃ n : ℕ, ∃ q : Fin (n + 1) → A.V,
      q 0 = u ∧ q (Fin.last n) = v ∧
      (∀ i : Fin n, ∃ fs, IntrinsicDirectedEdgeListPath A S missing
        (q i.castSucc) (q i.succ) fs ∧ fs.length = 1) ∧
      ∀ i, q i = u ∨ ∃ e ∈ es, ∃ he : ¬ A.map.missing e, A.map.head ⟨e, he⟩ = q i := by
  induction p with
  | nil => exact ⟨0, fun _ => u, rfl, rfl, Fin.elim0, fun _ => Or.inl rfl⟩
  | @snoc v es p e hs hm hv ih =>
    obtain ⟨n, q, hq0, hqlast, hstep, hverts⟩ := ih
    refine ⟨n + 1, Fin.snoc q (A.map.head e), ?_, Fin.snoc_last _ _, ?_, ?_⟩
    · exact (Fin.snoc_apply_zero _ _).trans hq0
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hi : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext rfl
        rw [Fin.snoc_castSucc, hi, Fin.snoc_last, hqlast]
        exact ⟨[e.val], (IntrinsicDirectedEdgeListPath.nil v).snoc e hs hm hv, rfl⟩
      · have hi : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
        rw [Fin.snoc_castSucc, hi, Fin.snoc_castSucc]
        exact hstep j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Or.inr ⟨e.val, List.mem_append_right _ (List.mem_singleton_self _),
          e.property, by rw [Fin.snoc_last]⟩
      · rw [Fin.snoc_castSucc]
        rcases hverts j with h | ⟨f, hf, hfp, hhead⟩
        · exact Or.inl h
        · exact Or.inr ⟨f, List.mem_append_left _ hf, hfp, hhead⟩

/-- Helper toward Proposition 3.9: the intrinsic version of Lemma 5.3,
quantifying over every actual s41 edge-list path. Visiting means being the
initial vertex or a directed head of one of its individual listed edges.
The common vertex sequence precedes both the intermediate label and endpoints. -/
@[expose] def IntrinsicConsumerCutVertices (A : D39DomainRootedMap.{0})
    (C : IntrinsicFutureCut2 A) : Prop :=
  ∀ k k' : ℤ, k < k' →
    ∃ v : ℕ → A.V, Function.Injective v ∧ (∀ m, v m ∈ C.vertices) ∧
      ∀ ell : ℤ, ell ∈ Set.Icc k k' →
        ∀ y : ℕ → A.V, Function.Injective y →
          (∀ j, ∃ es, IntrinsicDirectedEdgeListPath A C.edges C.missing (C.x ell) (y j) es) →
          ∀ m, ∃ J, ∀ j, J ≤ j →
            ∀ es : List A.E,
              IntrinsicDirectedEdgeListPath A C.edges C.missing (C.x ell) (y j) es →
              v m = C.x ell ∨
                ∃ e ∈ es, ∃ he : ¬ A.map.missing e, A.map.head ⟨e, he⟩ = v m

/-- Helper toward Proposition 3.9: every intrinsic cut in every representative
of a sampled class satisfies Lemma 5.3, on one iid event. Uniqueness is among
all intrinsic cuts, rather than cuts with an extra code-image hypothesis. -/
theorem intrinsicConsumers53_sample :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
        ∃! C : IntrinsicFutureCut2 A, IntrinsicConsumerCutVertices A C := by
  filter_upwards [uibotCut2_sample_unique_realization,
    DirectedDistances.Paper.Section5.lem_infty_cut] with W hreal hcut
  dsimp only at hreal hcut ⊢
  obtain ⟨H, h, hpast, hp, hrep⟩ := hreal
  obtain ⟨H', h', hLL', _, hcut⟩ := hcut
  have hH : H' = H := Subsingleton.elim _ _
  subst H'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let D := m0CutData W H h (fun _ _ => hp _)
  change ∀ k k' : ℤ, k < k' → _ at hcut
  refine ⟨H, h, hpast, hp, ?_⟩
  intro A hA
  obtain ⟨hI, C, hC, _⟩ := hrep A hA
  obtain ⟨I⟩ := hI
  obtain ⟨C', hv, he, _, _, hm, _, _, hx, _⟩ :=
    uibotCut2_in_representative W H h hpast hp A I
  have hCC := hC.1 C'
  subst C'
  have hmissing : C.missing = fun e => D.missing (I.edgeEquiv.symm e) := by
    funext e
    apply propext
    simpa only [Equiv.apply_symm_apply] using hm (I.edgeEquiv.symm e)
  have hlength (a b : A.V) (es : List A.E)
      (p : IntrinsicDirectedEdgeListPath A C.edges C.missing a b es) :
      m0CutReachableLength (m0CutDirectedStep W H D.seam) es.length
        (I.vertexEquiv.symm a) (I.vertexEquiv.symm b) := by
    rw [he, hmissing] at p
    let q := (intrinsicDirectedPathEquiv
      (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I D.edges D.missing
        (I.vertexEquiv.symm a) (I.vertexEquiv.symm b)).symm
      ⟨es, by
        change IntrinsicDirectedEdgeListPath A (I.edgeEquiv '' D.edges)
          (fun e => D.missing (I.edgeEquiv.symm e))
          (I.vertexEquiv (I.vertexEquiv.symm a)) (I.vertexEquiv (I.vertexEquiv.symm b)) es
        rw [I.vertexEquiv.apply_symm_apply, I.vertexEquiv.apply_symm_apply]
        exact p⟩
    apply (intrinsicDirected_source_lengths_iff W H G hp D _ _ es.length).mp
    exact ⟨q.val, q.property, List.length_map _⟩
  refine ⟨⟨I⟩, C, ?_, fun C' _ => hC.1 C'⟩
  intro k k' hkk
  obtain ⟨v, hvinj, hvmem, hforce⟩ := hcut k k' hkk
  refine ⟨fun m => I.vertexEquiv (v m), I.vertexEquiv.injective.comp hvinj, ?_, ?_⟩
  · intro m
    rw [hv]
    exact ⟨v m, hvmem m, rfl⟩
  · intro ell hell y hy hreach m
    have hy' : Function.Injective (fun j => I.vertexEquiv.symm (y j)) :=
      I.vertexEquiv.symm.injective.comp hy
    have hr : ∀ j, m0CutReachable W H D.seam (D.x ell)
        (I.vertexEquiv.symm (y j)) := by
      intro j
      obtain ⟨es, p⟩ := hreach j
      have hl := hlength _ _ es p
      rw [hx ell, Equiv.symm_apply_apply] at hl
      exact ⟨es.length, hl⟩
    obtain ⟨J, hJ⟩ := hforce ell hell (fun j => I.vertexEquiv.symm (y j)) hy' hr m
    refine ⟨J, ?_⟩
    intro j hj es hpath
    obtain ⟨n, p, hp0, hpn, hstep, hverts⟩ :=
      intrinsicConsumerPath_vertices A C.edges C.missing hpath
    obtain ⟨i, hi⟩ := hJ j hj n (fun i => I.vertexEquiv.symm (p i))
      (by rw [hp0, hx ell, Equiv.symm_apply_apply])
      (congrArg I.vertexEquiv.symm hpn) (fun i => by
        obtain ⟨es, hes, hlen⟩ := hstep i
        have hl := hlength _ _ es hes
        rw [hlen] at hl
        obtain ⟨a, ha, hs⟩ := hl
        exact ha ▸ hs)
    have hpi : p i = I.vertexEquiv (v m) :=
      (I.vertexEquiv.apply_symm_apply (p i)).symm.trans (congrArg I.vertexEquiv hi)
    rcases hverts i with hstart | ⟨e, he, hep, hhead⟩
    · exact Or.inl (hpi.symm.trans hstart)
    · exact Or.inr ⟨e, he, hep, hhead.trans hpi⟩

/-- Helper toward Proposition 3.9: one iid event supplies every
representative, every source isomorphism, all integer starts in Lemma 3.10
and Proposition 5.1, and Lemma 5.3 for the unique intrinsic cut. The dart
equivalence includes the source drawing's endpoint-side convention. -/
theorem intrinsicConsumers38And51And53_sample :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
        ∃! C : IntrinsicFutureCut2 A,
          (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
          IntrinsicConsumerCutVertices A C ∧
          ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
            (uibotWholePlaneSourceRoot W H G) A.map A.root,
            IntrinsicConsumerBoundary W A I.vertexEquiv I.edgeEquiv ∧
            IntrinsicConsumerFutureMaps W A I.vertexEquiv I.edgeEquiv
              ((uibotCut2SourceDartEquiv W H h hpast hp).trans
                (intrinsicFutureDartEquiv (A := uibotWholePlaneSourceDomain W H G hp) I)) := by
  filter_upwards [intrinsicConsumers38_sample, intrinsicConsumers51_sample,
    intrinsicConsumers53_sample, uibotCut2_sample_existsUnique] with W hb hf hc hu
  dsimp only at hc hu ⊢
  obtain ⟨H, h, hpast, hp, hrep⟩ := hc
  refine ⟨H, h, hpast, hp, ?_⟩
  intro A hA
  obtain ⟨hI, C, hC, huniq⟩ := hrep A hA
  obtain ⟨C₀, _, huni₀⟩ := hu A hA
  have heq : C = C₀ := huni₀ C trivial
  have huni : ∀ C' : IntrinsicFutureCut2 A, C' = C :=
    fun C' => (huni₀ C' trivial).trans heq.symm
  refine ⟨hI, C, ⟨huni, hC, ?_⟩, ?_⟩
  · intro I
    exact ⟨hb A I.vertexEquiv I.edgeEquiv, hf A I.vertexEquiv I.edgeEquiv
      ((uibotCut2SourceDartEquiv W H h hpast hp).trans
        (intrinsicFutureDartEquiv (A := uibotWholePlaneSourceDomain W H
          (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp) I))⟩
  · intro C' hC'
    exact huniq C' hC'.2.1

end DirectedDistances.PaperProofs.Section3
end
