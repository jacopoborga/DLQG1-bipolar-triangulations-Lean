module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperAssembly













public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open scoped ENNReal

attribute [local instance 1100] presentDartQuiver

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
No positivity or finiteness assumption on the partition is needed for this identity. -/
theorem boltzmannSdpUpper_markedAtom {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) :
    rightVertexMarkedBoltzmannLaw r {q} =
      (rightVertexMarkedPartition r)⁻¹ * rightVertexMarkedWeight q := by
  classical
  rw [rightVertexMarkedBoltzmannLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_smul_dirac_singleton]

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
reversal: an edge-count-preserving bijection preserves the full marked law. -/
theorem boltzmannSdpUpper_measurePreserving_of_sizeEquiv {r : ℕ}
    (e : RightVertexMarkedBoltzmannSpace r ≃ RightVertexMarkedBoltzmannSpace r)
    (hsize : ∀ q, (e q).1.2.1 = q.1.2.1) :
    MeasurePreserving e (rightVertexMarkedBoltzmannLaw r)
      (rightVertexMarkedBoltzmannLaw r) := by
  classical
  refine ⟨measurable_of_countable e, ?_⟩
  apply Measure.ext_of_singleton
  intro q
  have hpre : e ⁻¹' ({q} : Set (RightVertexMarkedBoltzmannSpace r)) = {e.symm q} := by
    ext x
    change e x = q ↔ x = e.symm q
    exact e.eq_symm_apply.symm
  rw [Measure.map_apply (measurable_of_countable e) (measurableSet_singleton q),
    hpre, boltzmannSdpUpper_markedAtom, boltzmannSdpUpper_markedAtom]
  congr 1
  change (1 / 3 : ℝ≥0∞) ^ (e.symm q).1.2.1 = (1 / 3 : ℝ≥0∞) ^ q.1.2.1
  have hs := hsize (e.symm q)
  rw [e.apply_symm_apply] at hs
  rw [hs]

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
left-boundary mark; this does not change the map or reverse its arrows. -/
@[expose] def boltzmannSdpUpper_markReflection (r : ℕ) :
    RightVertexMarkedBoltzmannSpace r ≃ RightVertexMarkedBoltzmannSpace r where
  toFun q := ⟨q.1, q.2.rev⟩
  invFun q := ⟨q.1, q.2.rev⟩
  left_inv q := by cases q; simp only [Fin.rev_rev]; rfl
  right_inv q := by cases q; simp only [Fin.rev_rev]; rfl

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
the full marked Boltzmann law, including all edge counts and left lengths. -/
theorem boltzmannSdpUpper_measurePreserving_markReflection (r : ℕ) :
    MeasurePreserving (boltzmannSdpUpper_markReflection r)
      (rightVertexMarkedBoltzmannLaw r) (rightVertexMarkedBoltzmannLaw r) := by
  exact boltzmannSdpUpper_measurePreserving_of_sizeEquiv
    (boltzmannSdpUpper_markReflection r) (fun _ => rfl)

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
arrow-reversing vertex map. The individual arrows, including multiedges, are explicit. -/
@[expose] def boltzmannSdpUpper_reversePath
    {V W : Type*} [Quiver V] [Quiver W] (f : V → W)
    (edge : ∀ {a b : V}, (a ⟶ b) → (f b ⟶ f a)) {a : V} :
    ∀ {b : V}, Quiver.Path a b → Quiver.Path (f b) (f a)
  | _, .nil => .nil
  | _, .cons P e => (edge e).toPath.comp (boltzmannSdpUpper_reversePath f edge P)

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result. -/
theorem boltzmannSdpUpper_reversePath_length
    {V W : Type*} [Quiver V] [Quiver W] (f : V → W)
    (edge : ∀ {a b : V}, (a ⟶ b) → (f b ⟶ f a))
    {a b : V} (P : Quiver.Path a b) :
    (boltzmannSdpUpper_reversePath f edge P).length = P.length := by
  induction P with
  | nil => rfl
  | cons P e ih =>
      simp only [boltzmannSdpUpper_reversePath, Path.length_comp, Path.length_toPath,
        ih, Path.length_cons, Nat.add_comm]

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
obligation, entirely at vertex and arrow level. No law or path estimate is
assumed. Constructing this bijection still requires the full map reversal. -/
@[expose] def boltzmannSdpUpper_reversalClassGeometry : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    ∃ e : RightVertexMarkedBoltzmannSpace r ≃ RightVertexMarkedBoltzmannSpace r,
      (∀ q, (e q).1.2.1 = q.1.2.1) ∧
      ∀ q : RightVertexMarkedBoltzmannSpace r,
        ∃ f : MapVertex (e q).1.2.2.out.B.map → MapVertex q.1.2.2.out.B.map,
          (∀ a b, (a ⟶ b) → Nonempty (f b ⟶ f a)) ∧
          f (e q).1.2.2.out.B.source = q.1.2.2.out.B.sink ∧
          ∀ j : Fin ((e q).1.1 + 1), (e q).2 ≤ j →
            ∃ i : Fin (q.1.1 + 1), i ≤ q.2 ∧
              f (boltzmannSdpUpper_leftVertex (e q) j) =
                boltzmannSdpUpper_leftVertex q i

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
original marked-reversal proposition to the named OPEN vertex/arrow geometry.
Both measure preservation and the entire reversed-path construction are proved. -/
theorem boltzmannSdpUpper_markedReversal_of_classGeometry
    (h : boltzmannSdpUpper_reversalClassGeometry) : boltzmannSdpUpper_markedReversal := by
  classical
  intro r hr
  obtain ⟨e, hsize, hlocal⟩ := h r hr
  refine ⟨e, boltzmannSdpUpper_measurePreserving_of_sizeEquiv e hsize, ?_⟩
  intro q j hj P
  obtain ⟨f, hedge, hsource, hleft⟩ := hlocal q
  obtain ⟨i, hi, htarget⟩ := hleft j hj
  let Q := boltzmannSdpUpper_reversePath f (fun {a b} edge =>
    Classical.choice (hedge a b edge)) P
  have hlen : Q.length = P.length := boltzmannSdpUpper_reversePath_length _ _ P
  have castLength {a a' b b' : MapVertex q.1.2.2.out.B.map}
      (ha : a = a') (hb : b = b') (R : Quiver.Path a b) :
      (ha ▸ hb ▸ R).length = R.length := by
    cases ha
    cases hb
    rfl
  exact ⟨i, hi, htarget ▸ hsource ▸ Q, (castLength htarget hsource Q).trans hlen⟩

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
local lifting induction. The hypothesis preserves each arrow, and the conclusion
retains equality of paths, hence also the identity of parallel edges. -/
theorem boltzmannSdpUpper_liftPrefixOrHit
    {V W : Type*} [Quiver V] [Quiver W] (F : Prefunctor V W) (S : Set V)
    (hstep : ∀ a : V, a ∉ S → ∀ b : W, ∀ edge : F.obj a ⟶ b,
      ∃ c : V, ∃ lifted : a ⟶ c, ∃ hc : F.obj c = b, hc ▸ F.map lifted = edge)
    (a : V) {b : W} (P : Quiver.Path (F.obj a) b) :
    (∃ c ∈ S, ∃ Q : Quiver.Path a c, ∃ T : Quiver.Path (F.obj c) b,
      P = (F.mapPath Q).comp T) ∨
      ∃ c : V, c ∉ S ∧ ∃ hc : F.obj c = b, ∃ Q : Quiver.Path a c,
        hc ▸ F.mapPath Q = P := by
  classical
  induction P with
  | nil =>
      by_cases ha : a ∈ S
      · exact Or.inl ⟨a, ha, Path.nil, Path.nil, rfl⟩
      · exact Or.inr ⟨a, ha, rfl, Path.nil, rfl⟩
  | @cons b c P edge ih =>
      rcases ih with ⟨v, hv, Q, T, hP⟩ | ⟨v, hv, hFv, Q, hQ⟩
      · exact Or.inl ⟨v, hv, Q, T.cons edge, by rw [Path.comp_cons, ← hP]⟩
      · cases hFv
        obtain ⟨z, lifted, hz, he⟩ := hstep v hv c edge
        cases hz
        change F.mapPath Q = P at hQ
        change F.map lifted = edge at he
        have hmap : F.mapPath (Q.cons lifted) = P.cons edge := by
          rw [Prefunctor.mapPath_cons, hQ, he]
        by_cases hS : z ∈ S
        · exact Or.inl ⟨z, hS, Q.cons lifted, Path.nil, hmap.symm⟩
        · exact Or.inr ⟨z, hS, rfl, Q.cons lifted, hmap⟩

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
the terminal endpoint cannot lift outside the stopping set. -/
theorem boltzmannSdpUpper_liftPrefixUntil
    {V W : Type*} [Quiver V] [Quiver W] (F : Prefunctor V W) (S : Set V)
    (hstep : ∀ a : V, a ∉ S → ∀ b : W, ∀ edge : F.obj a ⟶ b,
      ∃ c : V, ∃ lifted : a ⟶ c, ∃ hc : F.obj c = b, hc ▸ F.map lifted = edge)
    (a : V) {b : W} (hend : ∀ c, F.obj c = b → c ∈ S)
    (P : Quiver.Path (F.obj a) b) :
    ∃ c ∈ S, ∃ Q : Quiver.Path a c, ∃ T : Quiver.Path (F.obj c) b,
      P = (F.mapPath Q).comp T ∧ Q.length ≤ P.length := by
  rcases boltzmannSdpUpper_liftPrefixOrHit F S hstep a P with
    ⟨c, hc, Q, T, hP⟩ | ⟨c, hc, hFc, _⟩
  · refine ⟨c, hc, Q, T, hP, ?_⟩
    have mapLength : ∀ {u v : V} (R : Quiver.Path u v),
        (F.mapPath R).length = R.length := by
      intro u v R
      induction R with
      | nil => rfl
      | cons R e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
    rw [hP, Path.length_comp, mapLength Q]
    exact Nat.le_add_right _ _
  · exact (hc (hend c hFc)).elim

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
expressed in the existing ordered boundary carrier, with both endpoints. -/
@[expose] def boltzmannSdpUpper_upperMarkedArc {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) : Set (MapVertex q.1.2.2.out.B.map) :=
  {v | ∃ j : Fin (q.1.1 + 1), q.2 ≤ j ∧ v = boltzmannSdpUpper_leftVertex q j}

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
condition: every preimage of the specified raw endpoint is at or above the mark.
This is a predicate, not a proof that an arbitrary embedding satisfies it. -/
@[expose] def boltzmannSdpUpper_endpointAboveMark {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) {W : Type*} [Quiver W]
    (F : Prefunctor (MapVertex q.1.2.2.out.B.map) W) (y : W) : Prop :=
  ∀ v, F.obj v = y →
    ∃ j : Fin (q.1.1 + 1), q.2 ≤ j ∧ v = boltzmannSdpUpper_leftVertex q j

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
and the length bound follow from one-arrow lifting away from the upper arc
and the separately named endpoint condition. Both geometric premises are explicit. -/
theorem boltzmannSdpUpper_interception_of_localGeometry {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) {W : Type*} [Quiver W]
    (F : Prefunctor (MapVertex q.1.2.2.out.B.map) W)
    (hstep : ∀ a : MapVertex q.1.2.2.out.B.map,
      a ∉ boltzmannSdpUpper_upperMarkedArc q → ∀ b : W, ∀ edge : F.obj a ⟶ b,
        ∃ c : MapVertex q.1.2.2.out.B.map, ∃ lifted : a ⟶ c,
          ∃ hc : F.obj c = b, hc ▸ F.map lifted = edge)
    {y : W} (hend : boltzmannSdpUpper_endpointAboveMark q F y)
    (P : Quiver.Path (F.obj q.1.2.2.out.B.source) y) :
    ∃ j : Fin (q.1.1 + 1), q.2 ≤ j ∧
      ∃ Q : Quiver.Path q.1.2.2.out.B.source (boltzmannSdpUpper_leftVertex q j),
        ∃ T : Quiver.Path (F.obj (boltzmannSdpUpper_leftVertex q j)) y,
          P = (F.mapPath Q).comp T ∧ Q.length ≤ P.length := by
  obtain ⟨v, ⟨j, hj, hv⟩, Q, T, hP, hQ⟩ :=
    boltzmannSdpUpper_liftPrefixUntil F (boltzmannSdpUpper_upperMarkedArc q)
      hstep q.1.2.2.out.B.source hend P
  subst v
  exact ⟨j, hj, Q, T, hP, hQ⟩

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
with no quantified paths or distance inequalities: identify the source, lift
individual outgoing arrows away from the upper marked arc, and place every
upper-cell-boundary preimage at or above the mark. The last condition is exactly
`boltzmannSdpUpper_endpointAboveMark`; none of these geometric claims is asserted. -/
@[expose] def boltzmannSdpUpper_localExitGeometry : Prop :=
  ∀ᵐ ω ∂iidCodeMeasure, ∀ r : ℕ, ∀ hr : 1 ≤ r, ∀ n : ℕ,
    (∃ k ≤ n, R (fun i => ω (i + 1)) k = -(r : ℤ)) →
    let q := stoppedMarked r hr (quadrantHatWalk ω)
    ∃ F : Prefunctor (MapVertex q.1.2.2.out.B.map)
        (StagePresentVertex (fun i => ω (i + 1)) n),
      F.obj q.1.2.2.out.B.source = ⟨0⟩ ∧
      (∀ a : MapVertex q.1.2.2.out.B.map,
        a ∉ boltzmannSdpUpper_upperMarkedArc q →
        ∀ b : StagePresentVertex (fun i => ω (i + 1)) n, ∀ edge : F.obj a ⟶ b,
          ∃ c : MapVertex q.1.2.2.out.B.map, ∃ lifted : a ⟶ c,
            ∃ hc : F.obj c = b, hc ▸ F.map lifted = edge) ∧
      ∀ y : ℕ,
        (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).UL ++
            (kmswStage (fun i => ω (i + 1)) n).UR,
          (kmswStage (fun i => ω (i + 1)) n).west e = y ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = y) →
        boltzmannSdpUpper_endpointAboveMark q F ⟨y⟩




theorem boltzmannSdpUpper_cellPathInterception_of_localExitGeometry
    (h : boltzmannSdpUpper_localExitGeometry) : boltzmannSdpUpper_cellPathInterception := by
  filter_upwards [h] with ω hω
  intro r hr n hhit y hy P
  obtain ⟨F, hsource, hstep, hend⟩ := hω r hr n hhit
  let P' : Quiver.Path (F.obj (stoppedMarked r hr (quadrantHatWalk ω)).1.2.2.out.B.source)
      (⟨y⟩ : StagePresentVertex (fun i => ω (i + 1)) n) := hsource.symm ▸ P
  obtain ⟨j, hj, Q, _, _, hQ⟩ :=
    boltzmannSdpUpper_interception_of_localGeometry _ F hstep (hend y hy) P'
  have castLength {a a' b : StagePresentVertex (fun i => ω (i + 1)) n}
      (ha : a = a') (S : Quiver.Path a b) : (ha ▸ S).length = S.length := by
    cases ha
    rfl
  exact ⟨j, hj, Q, hQ.trans_eq (castLength hsource.symm P)⟩

end DirectedDistances.PaperProofs.Section7
