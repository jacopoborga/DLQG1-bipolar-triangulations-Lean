/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.LRIndClassPredicates
public import DirectedDistances.PlanarMap.FiniteXDPLeftmostLocal

/-! # Isomorphism invariance of lexicographically leftmost XDP geodesics

Helpers toward `lem-lr-ind`; not the paper result -/

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D']
variable {ℓ r : ℕ}

private theorem rotSymm_comm
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv (B.map.toCombinatorialMap.rot.symm d) =
      B'.map.toCombinatorialMap.rot.symm (I.toEquiv d) := by
  apply B'.map.toCombinatorialMap.rot.injective
  calc
    B'.map.toCombinatorialMap.rot
        (I.toEquiv (B.map.toCombinatorialMap.rot.symm d)) =
        I.toEquiv (B.map.toCombinatorialMap.rot
          (B.map.toCombinatorialMap.rot.symm d)) := (I.rot_comm _).symm
    _ = I.toEquiv d := by simp
    _ = B'.map.toCombinatorialMap.rot
        (B'.map.toCombinatorialMap.rot.symm (I.toEquiv d)) := by simp

private theorem rotSymm_pow_comm
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (n : ℕ) (d : D) :
    I.toEquiv ((B.map.toCombinatorialMap.rot.symm ^ n) d) =
      (B'.map.toCombinatorialMap.rot.symm ^ n) (I.toEquiv d) := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply]
      exact (ih (B.map.toCombinatorialMap.rot.symm d)).trans
        (congrArg _ (rotSymm_comm I d))

private theorem rotSymm_order_eq
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    orderOf B.map.toCombinatorialMap.rot.symm =
      orderOf B'.map.toCombinatorialMap.rot.symm := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  constructor
  · intro h
    ext d
    have hh := rotSymm_pow_comm I n (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at hh
    rw [h] at hh
    simpa using hh.symm
  · intro h
    ext d
    have hh := rotSymm_pow_comm I n d
    rw [h] at hh
    exact I.toEquiv.injective hh

private theorem finiteRotationScan_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    finiteRotationScan B' (I.toEquiv d) =
      (finiteRotationScan B d).map I.toEquiv := by
  unfold finiteRotationScan
  rw [← rotSymm_order_eq I]
  calc
    List.ofFn (fun i : Fin (orderOf B.map.toCombinatorialMap.rot.symm) =>
        (B'.map.toCombinatorialMap.rot.symm ^ i.val) (I.toEquiv d)) =
        List.ofFn (fun i : Fin (orderOf B.map.toCombinatorialMap.rot.symm) =>
          I.toEquiv ((B.map.toCombinatorialMap.rot.symm ^ i.val) d)) := by
      congr 1
      funext i
      exact (rotSymm_pow_comm I i.val d).symm
    _ = (List.ofFn (fun i : Fin (orderOf B.map.toCombinatorialMap.rot.symm) =>
          (B.map.toCombinatorialMap.rot.symm ^ i.val) d)).map I.toEquiv :=
      List.ofFn_comp' _ _

private theorem map_filter_eq_of_pred
    {α β : Type*} (f : α → β)
    (p : α → Bool) (q : β → Bool)
    (hpq : ∀ a, q (f a) = p a) (l : List α) :
    (l.filter p).map f = (l.map f).filter q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases h : p a = true <;> simp [h, hpq a, ih]

private theorem map_eraseDups_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) :
    (l.eraseDups).map f = (l.map f).eraseDups := by
  classical
  suffices h : ∀ n : ℕ, ∀ l : List α, l.length = n →
      (l.eraseDups).map f = (l.map f).eraseDups by
    exact h l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro l hl
      cases l with
      | nil => rfl
      | cons a t =>
          simp only [List.length_cons] at hl
          let p : α → Bool := fun b => !(b == a)
          let q : β → Bool := fun b => !(b == f a)
          rw [List.eraseDups_cons]
          simp only [List.map_cons]
          rw [List.eraseDups_cons]
          have hpq : ∀ b, q (f b) = p b := by
            intro b
            simp [p, q, hf.eq_iff]
          have hfilter : (t.filter p).map f = (t.map f).filter q :=
            map_filter_eq_of_pred f p q hpq t
          calc
            f a :: ((t.filter p).eraseDups).map f =
                f a :: ((t.filter p).map f).eraseDups := by
              congr 1
              exact ih ((t.filter p).length) (by
                have hle := List.length_filter_le p t
                omega) (t.filter p) rfl
            _ = f a :: ((t.map f).filter q).eraseDups := by
              rw [hfilter]

private theorem idxOf_map_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) :
    ∀ (l : List α) (a : α), (l.map f).idxOf (f a) = l.idxOf a := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons b t ih =>
      intro a
      by_cases h : b = a
      · subst a
        simp
      · have h' : f b ≠ f a := fun hEq => h (hf hEq)
        simp [h, h', ih]

/-- The leftmost outgoing dart is preserved by a boundary isomorphism
(`lem-lr-ind`; helper toward the paper result, -/
theorem leftmostOutgoing_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map)
    (hvs : v ≠ B.sink) :
    I.toEquiv (leftmostOutgoing B v hvs) =
      leftmostOutgoing B' (I.vertexEquiv v)
        (by
          intro h
          exact hvs (I.vertexEquiv.injective
            (h.trans I.vertexEquiv_sink.symm))) := by
  let hvs' : I.vertexEquiv v ≠ B'.sink := by
    intro h
    exact hvs (I.vertexEquiv.injective (h.trans I.vertexEquiv_sink.symm))
  by_cases hs : v = B.source
  · subst v
    have hsource : I.toEquiv
        (leftmostOutgoing B B.source hvs) =
          leftmostOutgoing B' B'.source (bipolar_source_ne_sink B') := by
      calc
        I.toEquiv (leftmostOutgoing B B.source hvs) =
            I.toEquiv (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) :=
          congrArg I.toEquiv (leftmostOutgoing_source_eq_firstLeftDart B)
        _ = B'.leftPath.firstDart (Nat.zero_lt_of_lt B'.left_length_pos) := by
          simp only [SimpleDirectedDartPath.firstDart, List.get_eq_getElem,
            ← I.leftDarts, List.getElem_map]
        _ = leftmostOutgoing B' B'.source (bipolar_source_ne_sink B') :=
          (leftmostOutgoing_source_eq_firstLeftDart B').symm
    simpa only [I.vertexEquiv_source] using hsource
  · have hs' : I.vertexEquiv v ≠ B'.source := by
      intro h
      exact hs (I.vertexEquiv.injective (h.trans I.vertexEquiv_source.symm))
    have hchar := leftmostOutgoing_internal_characterization B v hs hvs
    have hchar' := leftmostOutgoing_internal_characterization B'
      (I.vertexEquiv v) hs' hvs'
    apply hchar'.2.2.2 (I.toEquiv (leftmostOutgoing B v hvs))
    · calc
        dartTailVertex B'.map (I.toEquiv (leftmostOutgoing B v hvs)) =
            I.vertexEquiv (dartTailVertex B.map (leftmostOutgoing B v hvs)) :=
          (I.vertexEquiv_dartTailVertex _).symm
        _ = I.vertexEquiv v := congrArg I.vertexEquiv hchar.1
    · exact (I.tail_iff _).2 hchar.2.1
    · rw [← I.rot_comm]
      exact fun h => hchar.2.2.1 ((I.tail_iff _).mp h)

/-- The finite outgoing rotation order transports by mapping dart identities
(`lem-lr-ind`; helper toward the paper result, -/
theorem finiteOutgoingRotationOrder_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    finiteOutgoingRotationOrder B' (I.toEquiv d) =
      (finiteOutgoingRotationOrder B d).map I.toEquiv := by
  classical
  rw [finiteOutgoingRotationOrder, finiteOutgoingRotationOrder,
    finiteRotationScan_map I]
  symm
  apply map_filter_eq_of_pred I.toEquiv
    (fun e => decide (dartTailVertex B.map e = dartTailVertex B.map d ∧ B.map.tail e))
    (fun e => decide (dartTailVertex B'.map e = dartTailVertex B'.map (I.toEquiv d) ∧
      B'.map.tail e))
  · intro e
    let pt : Prop := dartTailVertex B'.map (I.toEquiv e) =
      dartTailVertex B'.map (I.toEquiv d) ∧ B'.map.tail (I.toEquiv e)
    let ps : Prop := dartTailVertex B.map e = dartTailVertex B.map d ∧ B.map.tail e
    change decide pt = decide ps
    have hp : pt ↔ ps := by
      constructor
      · rintro ⟨ht, hout⟩
        have ht' : I.vertexEquiv (dartTailVertex B.map e) =
            I.vertexEquiv (dartTailVertex B.map d) := by
          rw [I.vertexEquiv_dartTailVertex, I.vertexEquiv_dartTailVertex]
          exact ht
        exact ⟨I.vertexEquiv.injective ht', (I.tail_iff e).mp hout⟩
      · rintro ⟨ht, hout⟩
        exact ⟨by
          calc
            dartTailVertex B'.map (I.toEquiv e) =
                I.vertexEquiv (dartTailVertex B.map e) :=
              (I.vertexEquiv_dartTailVertex e).symm
            _ = I.vertexEquiv (dartTailVertex B.map d) := congrArg I.vertexEquiv ht
            _ = dartTailVertex B'.map (I.toEquiv d) := I.vertexEquiv_dartTailVertex d,
          (I.tail_iff e).mpr hout⟩
    by_cases hs : ps
    · have ht := hp.mpr hs
      simp [pt, ps, hs, ht]
    · have ht : ¬ pt := fun h => hs (hp.mp h)
      simp [pt, ps, hs, ht]

/-- The canonical deduplicated outgoing order transports by mapping dart
identities (`lem-lr-ind`; helper toward the paper result, -/
theorem canonicalOutgoingOrder_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map)
    (hvs : v ≠ B.sink) :
    canonicalOutgoingOrder B' (I.vertexEquiv v)
        (by
          intro h
          exact hvs (I.vertexEquiv.injective
            (h.trans I.vertexEquiv_sink.symm))) =
      (canonicalOutgoingOrder B v hvs).map I.toEquiv := by
  rw [canonicalOutgoingOrder, canonicalOutgoingOrder]
  have hleft := leftmostOutgoing_map I v hvs
  rw [← hleft]
  rw [finiteOutgoingRotationOrder_map I (leftmostOutgoing B v hvs)]
  exact (map_eraseDups_of_injective I.toEquiv I.toEquiv.injective _).symm

/-- The canonical outgoing order preserves `idxOf` under a boundary
isomorphism (`lem-lr-ind`; helper toward the paper result, -/
theorem canonicalOutgoingOrder_idxOf_map
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map)
    (hvs : v ≠ B.sink) (d : D) :
    (canonicalOutgoingOrder B' (I.vertexEquiv v)
      (by
        intro h
        exact hvs (I.vertexEquiv.injective
          (h.trans I.vertexEquiv_sink.symm)))).idxOf (I.toEquiv d) =
      (canonicalOutgoingOrder B v hvs).idxOf d := by
  rw [canonicalOutgoingOrder_map]
  exact idxOf_map_of_injective I.toEquiv I.toEquiv.injective _ _

/-- The path induced by a boundary isomorphism, with every dart and vertex
mapped along its corresponding equivalence. Helper toward `lem-lr-ind`, not -/
@[expose] noncomputable def BipolarBoundaryBaseIso.mapPath
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    SimpleDirectedDartPath B'.map B'.source B'.sink n where
  darts := P.darts.map I.toEquiv
  vertices := P.vertices.map I.vertexEquiv
  darts_length := by simp [P.darts_length]
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map I.vertexEquiv.injective
  start_vertex := by
    simpa using (congrArg I.vertexEquiv P.start_vertex).trans I.vertexEquiv_source
  end_vertex := by
    simpa using (congrArg I.vertexEquiv P.end_vertex).trans I.vertexEquiv_sink
  edge_step := by
    intro i
    have hiMap := i.isLt
    simp only [List.length_map] at hiMap
    have hi : i.val < n := by simpa [P.darts_length] using hiMap
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
    let jv : Fin P.vertices.length := ⟨i.val, by
      rw [P.vertices_length]
      omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by
      rw [P.vertices_length]
      omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map I.toEquiv).get i = I.toEquiv (P.darts.get j) := by
      simp [j]
    have hgetV : (P.vertices.map I.vertexEquiv).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv) := by simp [jv]
    have hgetV' : (P.vertices.map I.vertexEquiv).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv') := by simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hm
      exact h.1 ((I.missing_iff _).mp hm)
    · exact (I.tail_iff _).2 h.2.1
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv) := hgetV
        _ = I.vertexEquiv (dartTailVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.1
        _ = dartTailVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartTailVertex _
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv') := hgetV'
        _ = I.vertexEquiv (dartHeadVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.2
        _ = dartHeadVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartHeadVertex _

/-- The dart list of the mapped path is the mapped dart list. Helper toward -/
theorem BipolarBoundaryBaseIso.mapPath_darts
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    (I.mapPath P).darts = P.darts.map I.toEquiv := rfl

/-- A path is an XDP geodesic exactly when its image under a boundary
isomorphism is (`lem-lr-ind`; helper toward the paper result, -/
theorem isXDPGeodesicBase_iff_mapPath
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsXDPGeodesicBase B' x (I.mapPath P) ↔ IsXDPGeodesicBase B x P := by
  cases x with
  | ldp =>
      simp only [IsXDPGeodesicBase, isLDPGeodesicBase_iff_length_eq]
      rw [ldpLengthBase_eq_of_baseIso I]
  | sdp =>
      simp only [IsXDPGeodesicBase, isSDPGeodesicBase_iff_length_eq]
      rw [sdpLengthBase_eq_of_baseIso I]

private theorem isXDPGeodesicBase_congr_path
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    (x : XDP) {n : ℕ}
    (P Q : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsXDPGeodesicBase B x P ↔ IsXDPGeodesicBase B x Q := by
  cases x <;> rfl

/-- `IsLexLeftmostXDPGeodesic` is invariant under the boundary dart and
vertex equivalences (`lem-lr-ind`; helper toward the paper result, -/
theorem isLexLeftmostXDPGeodesic_mapPath_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP) {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsLexLeftmostXDPGeodesic B' x (I.mapPath P) ↔
      IsLexLeftmostXDPGeodesic B x P := by
  classical
  constructor
  · rintro ⟨hPgeo', hPlex'⟩
    refine ⟨(isXDPGeodesicBase_iff_mapPath I x P).mp hPgeo', ?_⟩
    intro m Q hQ hne hnm i htake hdiff
    let Q' := I.mapPath Q
    have hQgeo' : IsXDPGeodesicBase B' x Q' :=
      (isXDPGeodesicBase_iff_mapPath I x Q).mpr hQ
    have hne' : Q'.darts ≠ (I.mapPath P).darts := by
      intro heq
      apply hne
      apply List.map_injective_iff.mpr I.toEquiv.injective
      simpa [Q', BipolarBoundaryBaseIso.mapPath_darts] using heq
    have htake' : (I.mapPath P).darts.take i.val = Q'.darts.take i.val := by
      simpa only [Q', BipolarBoundaryBaseIso.mapPath_darts, List.map_take] using
        congrArg (fun ds => ds.map I.toEquiv) htake
    have hi : i.val < m := by omega
    let ip : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; omega⟩
    let iq : Fin Q.darts.length := ⟨i.val, by rw [Q.darts_length]; omega⟩
    let ip' : Fin (I.mapPath P).darts.length := ⟨i.val, by
      have hi' : i.val < n := i.isLt
      simpa only [(I.mapPath P).darts_length] using hi'⟩
    let iq' : Fin Q'.darts.length := ⟨i.val, by
      have hi' : i.val < m := by omega
      simpa only [Q'.darts_length] using hi'⟩
    have hp : (I.mapPath P).darts.get ip' = I.toEquiv (P.darts.get ip) := by
      simp [ip, ip', BipolarBoundaryBaseIso.mapPath_darts,
        List.get_eq_getElem, List.getElem_map]
    have hq : Q'.darts.get iq' = I.toEquiv (Q.darts.get iq) := by
      simp [iq, iq', Q', BipolarBoundaryBaseIso.mapPath_darts,
        List.get_eq_getElem, List.getElem_map]
    have hdiff' : (I.mapPath P).darts.get ip' ≠ Q'.darts.get iq' := by
      intro heq
      apply hdiff
      have heq' : I.toEquiv (P.darts.get ip) = I.toEquiv (Q.darts.get iq) := by
        rw [hp, hq] at heq
        exact heq
      simpa [ip, iq] using I.toEquiv.injective heq'
    obtain ⟨hvs', hlt'⟩ := hPlex' Q' hQgeo' hne' hnm i htake' hdiff'
    let d := P.darts.get ip
    let e := Q.darts.get iq
    have hvs : dartTailVertex B.map d ≠ B.sink := by
      intro h
      apply hvs'
      rw [hp]
      calc
        dartTailVertex B'.map (I.toEquiv d) = I.vertexEquiv (dartTailVertex B.map d) :=
          (I.vertexEquiv_dartTailVertex d).symm
        _ = I.vertexEquiv B.sink := congrArg I.vertexEquiv h
        _ = B'.sink := I.vertexEquiv_sink
    have hvsMapped : I.vertexEquiv (dartTailVertex B.map d) ≠ B'.sink := by
      intro h
      apply hvs
      exact I.vertexEquiv.injective (h.trans I.vertexEquiv_sink.symm)
    have hltCommon :
        (canonicalOutgoingOrder B' (I.vertexEquiv (dartTailVertex B.map d))
          (by
            intro h
            exact hvs (I.vertexEquiv.injective (h.trans I.vertexEquiv_sink.symm)))).idxOf
            (I.toEquiv d) <
        (canonicalOutgoingOrder B' (I.vertexEquiv (dartTailVertex B.map d))
          (by
            intro h
            exact hvs (I.vertexEquiv.injective (h.trans I.vertexEquiv_sink.symm)))).idxOf
            (I.toEquiv e) := by
      simpa only [d, e, ip', iq', hp, hq, Fin.val_mk,
        ← I.vertexEquiv_dartTailVertex] using hlt'
    rw [canonicalOutgoingOrder_idxOf_map I (dartTailVertex B.map d) hvs d,
      canonicalOutgoingOrder_idxOf_map I (dartTailVertex B.map d) hvs e] at hltCommon
    exact ⟨hvs, hltCommon⟩
  · rintro ⟨hPgeo, hPlex⟩
    refine ⟨(isXDPGeodesicBase_iff_mapPath I x P).mpr hPgeo, ?_⟩
    intro m Q' hQ' hne' hnm i htake' hdiff'
    let Q := I.symm.mapPath Q'
    have hQgeo : IsXDPGeodesicBase B x Q :=
      (isXDPGeodesicBase_iff_mapPath I.symm x Q').mpr hQ'
    have hQmap : Q.darts.map I.toEquiv = Q'.darts := by
      change (Q'.darts.map I.toEquiv.symm).map I.toEquiv = Q'.darts
      rw [List.map_map]
      simp
    have hPmap : P.darts.map I.toEquiv = (I.mapPath P).darts :=
      (BipolarBoundaryBaseIso.mapPath_darts I P).symm
    have hne : Q.darts ≠ P.darts := by
      intro heq
      apply hne'
      calc
        Q'.darts = Q.darts.map I.toEquiv := hQmap.symm
        _ = P.darts.map I.toEquiv := congrArg (fun ds => ds.map I.toEquiv) heq
        _ = (I.mapPath P).darts := hPmap
    have htakeMap : (P.darts.take i.val).map I.toEquiv =
        (Q.darts.take i.val).map I.toEquiv := by
      simpa only [List.map_take, hPmap, hQmap] using htake'
    have htake : P.darts.take i.val = Q.darts.take i.val :=
      (List.map_injective_iff.mpr I.toEquiv.injective) htakeMap
    have hi : i.val < m := by omega
    let ip : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; omega⟩
    let iq : Fin Q.darts.length := ⟨i.val, by rw [Q.darts_length]; omega⟩
    let ip' : Fin (I.mapPath P).darts.length := ⟨i.val, by
      have hi' : i.val < n := i.isLt
      simpa only [(I.mapPath P).darts_length] using hi'⟩
    let iq' : Fin Q'.darts.length := ⟨i.val, by
      have hi' : i.val < m := by omega
      simpa only [Q'.darts_length] using hi'⟩
    have hgetP : (I.mapPath P).darts.get ip' = I.toEquiv (P.darts.get ip) := by
      simp [ip, ip', BipolarBoundaryBaseIso.mapPath_darts,
        List.get_eq_getElem, List.getElem_map]
    have hiQ' : i.val < Q'.darts.length := by rw [Q'.darts_length]; omega
    have hiQ : i.val < Q.darts.length := by rw [Q.darts_length]; omega
    have hiQMap : i.val < (Q.darts.map I.toEquiv).length := by
      rw [List.length_map, Q.darts_length]
      exact hi
    have hgetQelem : Q'.darts[i.val]'hiQ' =
        (Q.darts.map I.toEquiv)[i.val]'hiQMap :=
      List.getElem_of_eq hQmap.symm hiQ'
    have hgetQ : Q'.darts.get iq' = I.toEquiv (Q.darts.get iq) := by
      change Q'.darts[i.val]'hiQ' = I.toEquiv (Q.darts[i.val]'hiQ)
      calc
        Q'.darts[i.val]'hiQ' = (Q.darts.map I.toEquiv)[i.val]'hiQMap := hgetQelem
        _ = I.toEquiv (Q.darts[i.val]'hiQ) := by simp only [List.getElem_map]
    have hgetQelemDirect : Q'.darts[i.val]'hiQ' =
        I.toEquiv (Q.darts[i.val]'hiQ) := by
      calc
        Q'.darts[i.val]'hiQ' = (Q.darts.map I.toEquiv)[i.val]'hiQMap := hgetQelem
        _ = I.toEquiv (Q.darts[i.val]'hiQ) := by simp only [List.getElem_map]
    have hdiff : P.darts.get ip ≠ Q.darts.get iq := by
      intro heq
      apply hdiff'
      have heq' : I.toEquiv (P.darts.get ip) = I.toEquiv (Q.darts.get iq) :=
        congrArg I.toEquiv heq
      rw [hgetP, hgetQ, heq']
    obtain ⟨hvs, hlt⟩ := hPlex Q hQgeo hne hnm i htake hdiff
    let d := P.darts.get ip
    let e := Q.darts.get iq
    have hvsMapped : I.vertexEquiv (dartTailVertex B.map d) ≠ B'.sink := by
      intro h
      apply hvs
      apply I.vertexEquiv.injective
      calc
        I.vertexEquiv (dartTailVertex B.map d) = B'.sink := h
        _ = I.vertexEquiv B.sink := I.vertexEquiv_sink.symm
    have hltCommon :
        (canonicalOutgoingOrder B' (I.vertexEquiv (dartTailVertex B.map d)) hvsMapped).idxOf
            (I.toEquiv d) <
        (canonicalOutgoingOrder B' (I.vertexEquiv (dartTailVertex B.map d)) hvsMapped).idxOf
            (I.toEquiv e) := by
      rw [canonicalOutgoingOrder_idxOf_map I (dartTailVertex B.map d) hvs d,
        canonicalOutgoingOrder_idxOf_map I (dartTailVertex B.map d) hvs e]
      exact hlt
    have hvs' : dartTailVertex B'.map (I.toEquiv d) ≠ B'.sink := by
      simpa only [hgetP, ← I.vertexEquiv_dartTailVertex] using hvsMapped
    have hvsPath' : dartTailVertex B'.map ((I.mapPath P).darts.get ip') ≠ B'.sink := by
      rw [hgetP]
      exact hvs'
    have hiP : i.val < P.darts.length := by rw [P.darts_length]; omega
    have hiPMap : i.val < (P.darts.map I.toEquiv).length := by
      rw [List.length_map]
      exact hiP
    have hgetPelem : (I.mapPath P).darts[i.val]'(by
        simpa only [BipolarBoundaryBaseIso.mapPath_darts, List.length_map] using hiPMap) =
        I.toEquiv (P.darts[i.val]'hiP) := by
      have hget : (P.darts.map I.toEquiv)[i.val]'hiPMap =
          I.toEquiv (P.darts[i.val]'hiP) := by
        simp only [List.getElem_map]
      simpa only [BipolarBoundaryBaseIso.mapPath_darts] using hget
    refine ⟨hvsPath', ?_⟩
    simpa only [List.get_eq_getElem, d, e, ip, iq, Fin.val_mk,
      hgetPelem, hgetQelemDirect, List.getElem_map,
      ← I.vertexEquiv_dartTailVertex] using hltCommon

/-- Any two lexicographically leftmost XDP geodesics on isomorphic bases
have corresponding dart lists (`lem-lr-ind`; helper toward the paper result, -/
theorem dartLists_eq_of_isLexLeftmostXDPGeodesic_baseIso
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP) {n m : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink m)
    (hP : IsLexLeftmostXDPGeodesic B x P)
    (hP' : IsLexLeftmostXDPGeodesic B' x P') :
    P'.darts = P.darts.map I.toEquiv := by
  have hmapped : IsLexLeftmostXDPGeodesic B' x (I.mapPath P) :=
    (isLexLeftmostXDPGeodesic_mapPath_iff I x P).2 hP
  have heq := dartLists_eq_of_isLexLeftmostXDPGeodesic B' x (I.mapPath P) P'
    hmapped hP'
  rw [BipolarBoundaryBaseIso.mapPath_darts] at heq
  exact heq.symm

end DirectedDistances.PlanarMap
