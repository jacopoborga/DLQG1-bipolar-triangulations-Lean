module

public import DirectedDistances.KMSW.PastLeftmostPathInduction
public import DirectedDistances.KMSW.StageLeftmostXDPIdentification
public import DirectedDistances.KMSW.StageInfiniteOutgoingOrder
public import DirectedDistances.KMSW.StageDirectedMapPathLengths
public import DirectedDistances.PaperProofs.Section4.FirstHitXDPIdentification

/-! canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result.

This module supplies prefix transport of code-path eligibility and of the eligible
outgoing order. The option-valued past selector also uses `recordVertex w N`, which
reads the next code, beyond the length-(N - 1) prefix. Its transport is separate. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap Quiver
open DirectedDistances.PaperProofs.Section3

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
private def prefixCodeMap (w w' : ℕ → Fin 3) (n : ℕ)
    (h : kmswStage w n = kmswStage w' n) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w' n) where
  obj v := ⟨v.id⟩
  map e := ⟨e.val, by simpa only [h] using e.property⟩

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem prefixCodeMap_length (w w' : ℕ → Fin 3) (n : ℕ)
    (h : kmswStage w n = kmswStage w' n) {a b : StagePresentVertex w n}
    (p : Path a b) : ((prefixCodeMap w w' n h).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem eligible_transport (w w' : ℕ → Fin 3) (n : ℕ)
    (h : kmswStage w n = kmswStage w' n) (x : XDP) (s t e : ℕ) :
    StageCodeXDPEligible w n x ⟨s⟩ ⟨t⟩ e →
      StageCodeXDPEligible w' n x ⟨s⟩ ⟨t⟩ e := by
  rintro ⟨a, b, f, hf, p, q, hg⟩
  let F := prefixCodeMap w w' n h
  let G := prefixCodeMap w' w n h.symm
  refine ⟨F.obj a, F.obj b, F.map f, hf, F.mapPath p, F.mapPath q, ?_⟩
  have hlen : (((F.mapPath p).cons (F.map f)).comp (F.mapPath q)).length =
      ((p.cons f).comp q).length := by
    simp only [Path.length_comp, Path.length_cons, prefixCodeMap_length, F]
  cases x with
  | ldp =>
    intro z
    have hz := hg (G.mapPath z)
    exact (prefixCodeMap_length w' w n h.symm z).symm.le.trans
      (hz.trans hlen.symm.le)
  | sdp =>
    intro z
    have hz := hg (G.mapPath z)
    exact hlen.le.trans
      (hz.trans (prefixCodeMap_length w' w n h.symm z).le)

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageCodeXDPEligible_iff_of_prefix (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) (x : XDP) (s t e : ℕ) :
    StageCodeXDPEligible w n x ⟨s⟩ ⟨t⟩ e ↔
      StageCodeXDPEligible w' n x ⟨s⟩ ⟨t⟩ e := by
  have hs := kmswStage_eq_of_prefix w w' n h
  exact ⟨eligible_transport w w' n hs x s t e,
    eligible_transport w' w n hs.symm x s t e⟩

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageEligibleOutgoingEdgeOrder_eq_of_prefix (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) (x : XDP) (s t : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEligibleOutgoingEdgeOrder w n x ⟨s⟩ ⟨t⟩ d =
      stageEligibleOutgoingEdgeOrder w' n x ⟨s⟩ ⟨t⟩
        ((kmswStageDirectedMapIsoOfPrefix w w' n h).toEquiv d) := by
  classical
  unfold stageEligibleOutgoingEdgeOrder
  rw [stageOutgoingEdgeOrder_eq_of_prefix w w' n h]
  congr 1
  funext e
  exact Bool.decide_congr (stageCodeXDPEligible_iff_of_prefix w w' n h x s t e)

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageEligibleOutgoingEdgeOrder_codeExtend {ℓ r N : ℕ}
    (c : KMSWWalkClass ℓ r N) (w : ℕ → Fin 3)
    (hc : ∀ i : Fin (N - 1), c.val i = w i.val) (x : XDP) (s t : ℕ)
    (d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge) :
    stageEligibleOutgoingEdgeOrder (codeExtend c) (N - 1) x ⟨s⟩ ⟨t⟩ d =
      stageEligibleOutgoingEdgeOrder w (N - 1) x ⟨s⟩ ⟨t⟩
        ((kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (N - 1)
          (fun i hi => (codeExtend_of_lt c i hi).trans (hc ⟨i, hi⟩))).toEquiv d) := by
  exact stageEligibleOutgoingEdgeOrder_eq_of_prefix (codeExtend c) w (N - 1)
    (fun i hi => (codeExtend_of_lt c i hi).trans (hc ⟨i, hi⟩)) x s t d

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageEligibleOutgoingEdgeOrder_stoppedWord (r : ℕ) (ω : ℕ → Fin 3)
    {ℓ : ℕ} (c : KMSWWalkClass ℓ r (boltzmannTau r ω))
    (hc : c.val = stoppedWord r ω) (x : XDP) (s t : ℕ)
    (d : StageDart (kmswStage (codeExtend c) (boltzmannTau r ω - 1)).nextEdge) :
    stageEligibleOutgoingEdgeOrder (codeExtend c) (boltzmannTau r ω - 1)
        x ⟨s⟩ ⟨t⟩ d =
      stageEligibleOutgoingEdgeOrder (boltzmannKMSWStream ω) (boltzmannTau r ω - 1)
        x ⟨s⟩ ⟨t⟩
        ((kmswStageDirectedMapIsoOfPrefix (codeExtend c) (boltzmannKMSWStream ω)
          (boltzmannTau r ω - 1) (fun i hi =>
            (codeExtend_of_lt c i hi).trans (congrFun hc ⟨i, hi⟩))).toEquiv d) := by
  exact stageEligibleOutgoingEdgeOrder_codeExtend c (boltzmannKMSWStream ω)
    (fun i => congrFun hc i) x s t d

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem zeroStage_path_end (w : ℕ → Fin 3)
    {a b : StagePresentVertex w 0} (p : Path a b) :
    b.id = a.id ∨ b.id = 1 := by
  cases p with
  | nil => exact Or.inl rfl
  | cons p f => exact Or.inr f.property.2.2.2.symm

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem zeroCode_pastStep (x : XDP) :
    pastStageLeftmostXDPStep (fun _ => 0) 1 x 0 = none := by
  classical
  unfold pastStageLeftmostXDPStep
  split
  next hc =>
    have hnil : stageEligibleOutgoingEdgeOrder (fun _ => 0) 0 x
        ⟨0⟩ ⟨2⟩ hc.choose = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      obtain ⟨_, hel⟩ := List.mem_filter.mp he
      obtain ⟨a, b, f, _, _, q, _⟩ := of_decide_eq_true hel
      have hb : b.id = 1 := f.property.2.2.2.symm
      rcases zeroStage_path_end (fun _ => 0) q with ht | ht
      · change 2 = b.id at ht
        omega
      · change 2 = 1 at ht
        omega
    change (stageEligibleOutgoingEdgeOrder (fun _ => 0) 0 x
      ⟨0⟩ ⟨2⟩ hc.choose).head? = none
    rw [hnil]
    rfl
  next _ => rfl

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem downCode_pastStep :
    pastStageLeftmostXDPStep (fun _ => 2) 1 .sdp 0 = some 0 := by
  classical
  let w : ℕ → Fin 3 := fun _ => 2
  have hc : ∃ d : StageDart (kmswStage w 0).nextEdge,
      (d = stageULHeadDart w 0 ∨
        d.2 = false ∧ (stageRot w 0 d).2 = true) ∧
      stageEndpoint (kmswStage w 0) d = 0 :=
    ⟨stageULHeadDart w 0, Or.inl rfl, rfl⟩
  change pastStageLeftmostXDPStep w 1 .sdp 0 = some 0
  unfold pastStageLeftmostXDPStep
  rw [dite_eq_left hc]
  have hd : hc.choose = stageULHeadDart w 0 := by
    rcases hc.choose_spec.1 with h | h
    · exact h
    · have hr : (stageRot w 0 hc.choose).2 = hc.choose.2 := rfl
      rw [hr, h.1] at h
      contradiction
  rw [hd]
  have hel : StageCodeXDPEligible w 0 .sdp ⟨0⟩ ⟨1⟩ 0 := by
    let f := initialEdgeArrow w 0
    refine ⟨⟨0⟩, ⟨1⟩, f, rfl, Path.nil, Path.nil, ?_⟩
    intro q
    have hpos : 0 < q.length := by
      by_contra hn
      have he := q.eq_of_length_zero (by omega)
      have hid := congrArg StagePresentVertex.id he
      change 0 = 1 at hid
      omega
    change 1 ≤ q.length
    omega
  have ho : stageOutgoingEdgeOrder w 0 (stageULHeadDart w 0) = [0] := by
    have hs : (stageRot w 0).symm = 1 := rfl
    unfold stageOutgoingEdgeOrder stageOutgoingDartOrder
    rw [hs]
    simp only [orderOf_one, one_pow, Equiv.Perm.one_apply, List.ofFn_succ,
      List.ofFn_zero]
    simp [stageULHeadDart, kmswStage, kmswInit, stageEndpoint]
    rfl
  change (stageEligibleOutgoingEdgeOrder w 0 .sdp ⟨0⟩ ⟨1⟩
    (stageULHeadDart w 0)).head? = some 0
  simp only [stageEligibleOutgoingEdgeOrder, ho, List.filter_cons,
    decide_eq_true hel, List.filter_nil, ↓reduceIte, List.head?_cons]

/-- canonical leftmost XDP geodesic of the stopped KMSW map representative equals the
past-stage leftmost trace; T_m, F4c and both-mode scope are not treated; not the paper result.
The literal past selector is not determined by the length-(N - 1) prefix. -/
theorem pastStageLeftmostXDPStep_empty_prefix_counterexample :
    ∃ c : KMSWWalkClass 1 1 1,
      (∀ i : Fin (1 - 1), c.val i = (2 : Fin 3)) ∧
        pastStageLeftmostXDPStep (codeExtend c) 1 .sdp 0 = none ∧
        pastStageLeftmostXDPStep (fun _ => 2) 1 .sdp 0 = some 0 := by
  let c : KMSWWalkClass 1 1 1 := ⟨fun i => Fin.elim0 i, by
    constructor
    · rfl
    · intro k hk
      have hk0 : k = 0 := by
        change k ∈ Finset.range 1 at hk
        have := Finset.mem_range.mp hk
        omega
      subst k
      exact ⟨by decide, by decide⟩⟩
  have he : codeExtend c = fun _ => 0 := by
    funext i
    simp only [codeExtend, finiteCodeExtend, Nat.sub_self, Nat.not_lt_zero, ↓reduceDIte]
  refine ⟨c, fun i => Fin.elim0 i, ?_, downCode_pastStep⟩
  rw [he]
  exact zeroCode_pastStep .sdp

end DirectedDistances.KMSW
