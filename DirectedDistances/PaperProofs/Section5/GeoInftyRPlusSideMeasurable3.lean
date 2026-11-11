/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusSideMeasurable2

/-! # Measurability of permanent-ID ancestor images

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. Prefix transport preserves permanent vertex IDs. -/
theorem stageVertexId_trans_prefix
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    (w w' : ℕ → Fin 3) (t : ℕ) (h : ∀ i < t, w i = w' i)
    (I : DirectedMapWithMissingIso M (kmswStageDirectedMap w t)) (v : MapVertex M) :
    (stageMapVertex w' t (cutMapIsoVertexEquiv
      (I.trans (kmswStageDirectedMapIsoOfPrefix w w' t h)) v)).id =
    (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id := by
  refine Quotient.inductionOn v ?_
  intro d
  change stageEndpoint (kmswStage w' t)
      ((kmswStageDirectedMapIsoOfPrefix w w' t h).toEquiv (I.toEquiv d)) =
    stageEndpoint (kmswStage w t) (I.toEquiv d)
  obtain ⟨he, hb⟩ := kmswStageDirectedMapIsoOfPrefix_val w w' t h (I.toEquiv d)
  simp only [stageEndpoint, he, hb, ← kmswStage_eq_of_prefix w w' t h]

/-- Helper toward Lemma 5.5. A finite certificate retains its boundary lists,
the actual selected cut classes, the level target, and the permanent vertex ID. -/
@[expose] noncomputable def finiteAncestorVertexImage
    (x : XDP) (a : ThinMapSide) (s n t r : ℕ) (C : PositiveCutOutput)
    (w : ℕ → Fin 3) : Prop :=
  ∃ (ℓ m : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1)))
    (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
    (∀ b : ThinMapSide, (boundaryDarts R.B b).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match b with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) ∧
    (∀ b i, (boundaryTarget R.B b i).map
      (fun z => (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I z)).id) =
        match i with
        | 0 => some 0
        | j + 1 => ((match b with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR)[j]?).map
            (kmswStage w (t - 1)).east) ∧
    C =
      (some ⟨m, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
       some ⟨r, ⟨m, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
    boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v ∧
    n ∈ ancestorPosVertexId w (t - 1) R hR I a ''
      ancestors (presentation (ancestorPosHalfRep R hR a) a v)

/-- Helper toward Lemma 5.5. A finite image certificate transports along a
common code prefix without changing any permanent vertex ID. -/
theorem finiteAncestorVertexImage_of_prefix
    (x : XDP) (a : ThinMapSide) (s n t r : ℕ) (C : PositiveCutOutput)
    (w w' : ℕ → Fin 3) (h : ∀ i < t - 1, w i = w' i) :
    finiteAncestorVertexImage x a s n t r C w →
      finiteAncestorVertexImage x a s n t r C w' := by
  rintro ⟨ℓ, m, R, hR, I, v, hb, ht, hc, hv, z, hz, hzn⟩
  let J := kmswStageDirectedMapIsoOfPrefix w w' (t - 1) h
  refine ⟨ℓ, m, R, hR, I.trans J, v, ?_, ?_, hc, hv, z, hz, ?_⟩
  · intro b
    have he : (fun d => (((I.trans J).toEquiv d).1.val,
        ((I.trans J).toEquiv d).2)) =
        (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) := by
      funext d
      exact Prod.ext
        (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h (I.toEquiv d)).1
        (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h (I.toEquiv d)).2
    rw [he, hb b, ← kmswStage_eq_of_prefix w w' (t - 1) h]
  · intro b i
    have he : (fun z => (stageMapVertex w' (t - 1)
        (cutMapIsoVertexEquiv (I.trans J) z)).id) =
        (fun z => (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I z)).id) := by
      funext z
      exact stageVertexId_trans_prefix w w' (t - 1) h I z
    rw [he, ht b i]
    cases i <;> simp only [← kmswStage_eq_of_prefix w w' (t - 1) h]
  · exact (stageVertexId_trans_prefix w w' (t - 1) h I
      (ancestorPosVertexMap R hR a z)).trans hzn

/-- Helper toward Lemma 5.5. Fixed-ID finite image certificates are measurable
finite-prefix events. The target is a permanent ID rather than a quotient label. -/
theorem measurableSet_finiteAncestorVertexImage
    (x : XDP) (a : ThinMapSide) (s n t r : ℕ) (C : PositiveCutOutput) :
    MeasurableSet {w : ℕ → Fin 3 | finiteAncestorVertexImage x a s n t r C w} := by
  refine measurableSet_of_factors_prefix (t - 1) _ ?_
  intro w w' h
  exact ⟨finiteAncestorVertexImage_of_prefix x a s n t r C w w' h,
    finiteAncestorVertexImage_of_prefix x a s n t r C w' w (fun i hi => (h i hi).symm)⟩

local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
local notation "HL" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
local notation "HT" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
local notation "HR" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
local notation "P" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q)

/-- Helper toward Lemma 5.5. At a good cut, the finite certificate event is
exactly membership in the geometric ancestor carrier, including level zero. -/
theorem geometricAncestor_mem_iff_finiteImage
    (x : XDP) (q : Coherent x) (a : ThinMapSide) (s n k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2)) :
    n ∈ geometricAncestorVertices x renewalTime renewalTime_positiveSuccessTime a q s ↔
      finiteAncestorVertexImage x a s n
        (selectedCutTime renewalTime (k + 1) q.1).toNat
        (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat
        (selectedCutPastCuts x renewalTime (k + 1) q.1) (W q) := by
  let t := (selectedCutTime renewalTime (k + 1) q.1).toNat
  let r := (-(q.1 t).2).toNat
  let F := fun {ℓ : ℕ} (R : KMSWMapRep ℓ r t)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap (W q) (t - 1))) =>
    fun z => (stageMapVertex (W q) (t - 1) (cutMapIsoVertexEquiv I z)).id
  have hrecord := selectedCut_past_boundary_target_record
    x renewalTime renewalTime_positiveSuccessTime q a k s hk
  have hidentify : ∀ (ℓ m : ℕ) (R : KMSWMapRep ℓ r t)
      (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap (W q) (t - 1)))
      (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
      (∀ b : ThinMapSide, (boundaryDarts R.B b).map
        (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
          (match b with
            | .left => (kmswStage (W q) (t - 1)).UL
            | .right => (kmswStage (W q) (t - 1)).LR).map (fun e => (e, false))) →
      (boundaryTarget R.B a s).map (F R I) =
        some (thinMapBoundaryVertex (W q) (HF x q) (HL x q) (HT x q) (HR x q) a s) →
      selectedCutPastCuts x renewalTime (k + 1) q.1 =
        (some ⟨m, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨m, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) →
      boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v →
      ancestorPosVertexId (W q) (t - 1) R hR I a ''
        ancestors (presentation (ancestorPosHalfRep R hR a) a v) =
          geometricAncestorVertices x renewalTime renewalTime_positiveSuccessTime a q s := by
    intro ℓ m R hR I v hb htarget hc hv
    have hh := congrArg (Option.map (F R I)) (ancestorPos_boundaryTarget_map R hR a s)
    rw [hv, Option.map_some, htarget] at hh
    have hvid : ancestorPosVertexId (W q) (t - 1) R hR I a v =
        thinMapBoundaryVertex (W q) (HF x q) (HL x q) (HT x q) (HR x q) a s :=
      Option.some.inj hh
    have hp := sourceAncestorPosHalf_path_prefix
      x renewalTime renewalTime_positiveSuccessTime q s k hk R hR I hb hc
    have hseed (b : ThinMapSide) :
        AncestorPosHalfOffPrefixArcSeedIdentification
          (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I b := by
      apply ancestorPos_arcSeeds_of_boundaryLaunch
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp b
      apply (ancestorPos_boundaryLaunch_iff_seamLaunch
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp b).mpr
      apply (ancestorPos_seamLaunch_iff_argumentOrder
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp b).mpr
      exact fun i => ancestorPos_seamLaunch_argumentOrder
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp b i
    have hside := (ancestorPos_sideRanges_iff_arcSeeds
      (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp).mpr hseed
    have hg := sourceAncestorPosHalf_geometric_of_sideRange
      x renewalTime renewalTime_positiveSuccessTime q a s k hk R hR I v hvid hp (hside a)
    exact ancestorPos_vertices_image_of_darts
      (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q)
      (presentation (ancestorPosHalfRep R hR a) a v) a s
      (ancestorPosVertexId (W q) (t - 1) R hR I a)
      (ancestorPosDartId (W q) (t - 1) R hR I a)
      (fun d => (ancestorPos_ids_endpoints (W q) (t - 1) R hR I a d).1) hvid hg.1
  have htarget {ℓ : ℕ} (R : KMSWMapRep ℓ r t)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap (W q) (t - 1)))
      (ht : ∀ b i, (boundaryTarget R.B b i).map (F R I) =
        match i with
        | 0 => some 0
        | j + 1 => ((match b with
          | .left => (kmswStage (W q) (t - 1)).UL
          | .right => (kmswStage (W q) (t - 1)).LR)[j]?).map
            (kmswStage (W q) (t - 1)).east) :
      (boundaryTarget R.B a s).map (F R I) =
        some (thinMapBoundaryVertex (W q) (HF x q) (HL x q) (HT x q) (HR x q) a s) := by
    rw [ancestor_boundaryVertex_eq]
    cases s <;> exact (ht a _).trans hrecord
  constructor
  · intro hn
    obtain ⟨ℓ, m, R, hR, I, _, _, hb, ht, hc⟩ :=
      selectedCutPastCuts_representatives_boundary_stageIso
        x renewalTime renewalTime_positiveSuccessTime q k s hk
    have htg := htarget R I ht
    have hh := congrArg (Option.map (F R I)) (ancestorPos_boundaryTarget_map R hR a s)
    rw [htg, Option.map_map] at hh
    obtain ⟨v, hv, _⟩ := Option.map_eq_some_iff.mp hh
    refine ⟨ℓ, m, R, hR, I, v, hb, ht, hc, hv, ?_⟩
    rwa [hidentify ℓ m R hR I v hb htg hc hv]
  · rintro ⟨ℓ, m, R, hR, I, v, hb, ht, hc, hv, hn⟩
    rwa [hidentify ℓ m R hR I v hb (htarget R I ht) hc hv] at hn

/-- Helper toward Lemma 5.5. The finite certificate at each selected cut
is measurable on the coherent subtype, with its permanent vertex IDs. -/
theorem measurable_finiteAncestorVertexImage_at_cut
    (x : XDP) (a : ThinMapSide) (s n k : ℕ) :
    Measurable (fun q : Coherent x => decide (finiteAncestorVertexImage x a s n
      (selectedCutTime renewalTime (k + 1) q.1).toNat
      (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat
      (selectedCutPastCuts x renewalTime (k + 1) q.1) (W q))) := by
  let G : (ℕ × ℕ × PositiveCutOutput) × (ℕ → Fin 3) → Bool := fun z =>
    decide (finiteAncestorVertexImage x a s n z.1.1 z.1.2.1 z.1.2.2
      (boltzmannKMSWStream z.2))
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro z
    apply measurable_of_factors_prefix (z.1 + 1)
    intro c c' h
    apply Bool.decide_congr
    exact ⟨finiteAncestorVertexImage_of_prefix x a s n z.1 z.2.1 z.2.2
        _ _ (fun i hi => h (i + 1) (by omega)),
      finiteAncestorVertexImage_of_prefix x a s n z.1 z.2.1 z.2.2
        _ _ (fun i hi => (h (i + 1) (by omega)).symm)⟩
  have htime : Measurable (fun q : Coherent x =>
      (selectedCutTime renewalTime (k + 1) q.1).toNat) :=
    (measurable_of_countable ENat.toNat).comp
      ((measurable_selectedCutTime renewalTime (k + 1)
        renewalTime_positiveSuccessTime).comp measurable_subtype_coe)
  have heval : Measurable (fun q : Coherent x =>
      q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat) := by
    simpa only [selectedCutFuture, conditionedVectorShift, Nat.add_zero,
      Function.comp_def] using ((measurable_pi_apply 0).comp
        (measurable_selectedCutFuture renewalTime (k + 1)
          renewalTime_positiveSuccessTime)).comp measurable_subtype_coe
  have hr : Measurable (fun q : Coherent x =>
      (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat) :=
    (measurable_of_countable (fun j : ℤ => (-j).toNat)).comp heval.snd
  exact hG.comp ((htime.prodMk (hr.prodMk
    ((measurable_selectedCutPastCuts x renewalTime (k + 1)
      renewalTime_positiveSuccessTime).comp measurable_subtype_coe))).prodMk
        (measurable_pathCode.comp measurable_subtype_coe))

/-- Helper toward Lemma 5.5. Membership of a fixed permanent vertex ID in
one geometric ancestor level is measurable on the coherent subtype. -/
theorem measurableSet_geometricAncestorVertices
    (x : XDP) (a : ThinMapSide) (s n : ℕ) :
    MeasurableSet {q : Coherent x | n ∈ geometricAncestorVertices
      x renewalTime renewalTime_positiveSuccessTime a q s} := by
  have hG : Measurable (fun z : ℕ × Coherent x =>
      decide (finiteAncestorVertexImage x a s n
        (selectedCutTime renewalTime (z.1 + 1) z.2.1).toNat
        (-(z.2.1 (selectedCutTime renewalTime (z.1 + 1) z.2.1).toNat).2).toNat
        (selectedCutPastCuts x renewalTime (z.1 + 1) z.2.1) (W z.2))) :=
    measurable_from_prod_countable_right
      (measurable_finiteAncestorVertexImage_at_cut x a s n)
  have h := hG.comp ((measurable_leastGoodCut x renewalTime
    renewalTime_positiveSuccessTime s).prodMk measurable_id)
  have he : (fun q : Coherent x => decide (n ∈ geometricAncestorVertices
      x renewalTime renewalTime_positiveSuccessTime a q s)) =
      (fun q : Coherent x => decide (finiteAncestorVertexImage x a s n
        (selectedCutTime renewalTime
          (leastGoodCut x renewalTime renewalTime_positiveSuccessTime s q + 1) q.1).toNat
        (-(q.1 (selectedCutTime renewalTime
          (leastGoodCut x renewalTime renewalTime_positiveSuccessTime s q + 1) q.1).toNat).2).toNat
        (selectedCutPastCuts x renewalTime
          (leastGoodCut x renewalTime renewalTime_positiveSuccessTime s q + 1) q.1) (W q))) := by
    funext q
    exact Bool.decide_congr (geometricAncestor_mem_iff_finiteImage x q a s n _
      (leastGoodCut_spec x renewalTime renewalTime_positiveSuccessTime s q))
  have hm : Measurable (fun q : Coherent x => decide (n ∈ geometricAncestorVertices
      x renewalTime renewalTime_positiveSuccessTime a q s)) := he.symm ▸ h
  have hh := hm (measurableSet_singleton true)
  change MeasurableSet {q : Coherent x | decide (n ∈ geometricAncestorVertices
    x renewalTime renewalTime_positiveSuccessTime a q s) = true} at hh
  simpa only [decide_eq_true_eq] using hh

/-- Helper toward Lemma 5.5. Fixed-ID membership at a right ancestor level
is a measurable event. -/
theorem measurableSet_geometricRightAncestorVertices
    (x : XDP) (s n : ℕ) :
    MeasurableSet {q : Coherent x | n ∈ geometricAncestorVertices
      x renewalTime renewalTime_positiveSuccessTime .right q s} :=
  measurableSet_geometricAncestorVertices x .right s n

/-- Helper toward Lemma 5.5. The full right vertex carrier is the countable
union of its measurable geometric ancestor levels. -/
theorem measurable_geometricRightSide_vertices (x : XDP) (n : ℕ) :
    Measurable (fun q : Coherent x => decide (n ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).vertices)) := by
  have hm : MeasurableSet {q : Coherent x | n ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).vertices} := by
    change MeasurableSet {q : Coherent x | n ∈ ⋃ s,
      geometricAncestorVertices x renewalTime renewalTime_positiveSuccessTime .right q s}
    simp only [Set.mem_iUnion]
    simpa only [Set.iUnion_ofPred] using
      MeasurableSet.iUnion (fun s => measurableSet_geometricRightAncestorVertices x s n)
  have he : (fun q : Coherent x => decide (n ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).vertices)) =
      (fun q : Coherent x => if n ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).vertices
        then true else false) := by
    funext q
    split <;> simp_all only [decide_true, decide_false]
  rw [he]
  exact measurable_const.ite hm measurable_const

/-- Helper toward Lemma 5.5. A finite certificate retains its boundary lists,
the actual selected cut classes, the level target, and the permanent edge ID. -/
@[expose] noncomputable def finiteAncestorEdgeImage
    (x : XDP) (a : ThinMapSide) (s n t r : ℕ) (C : PositiveCutOutput)
    (w : ℕ → Fin 3) : Prop :=
  ∃ (ℓ m : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1)))
    (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
    (∀ b : ThinMapSide, (boundaryDarts R.B b).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match b with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) ∧
    (∀ b i, (boundaryTarget R.B b i).map
      (fun z => (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I z)).id) =
        match i with
        | 0 => some 0
        | j + 1 => ((match b with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR)[j]?).map
            (kmswStage w (t - 1)).east) ∧
    C =
      (some ⟨m, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
       some ⟨r, ⟨m, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
    boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v ∧
    (n, false) ∈ ancestorPosDartId w (t - 1) R hR I a ''
      selectedDarts (presentation (ancestorPosHalfRep R hR a) a v)

/-- Helper toward Lemma 5.5. A finite image certificate transports along a
common code prefix without changing any permanent edge ID. -/
theorem finiteAncestorEdgeImage_of_prefix
    (x : XDP) (a : ThinMapSide) (s n t r : ℕ) (C : PositiveCutOutput)
    (w w' : ℕ → Fin 3) (h : ∀ i < t - 1, w i = w' i) :
    finiteAncestorEdgeImage x a s n t r C w →
      finiteAncestorEdgeImage x a s n t r C w' := by
  rintro ⟨ℓ, m, R, hR, I, v, hb, ht, hc, hv, z, hz, hzn⟩
  let J := kmswStageDirectedMapIsoOfPrefix w w' (t - 1) h
  refine ⟨ℓ, m, R, hR, I.trans J, v, ?_, ?_, hc, hv, z, hz, ?_⟩
  · intro b
    have he : (fun d => (((I.trans J).toEquiv d).1.val,
        ((I.trans J).toEquiv d).2)) =
        (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) := by
      funext d
      exact Prod.ext
        (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h (I.toEquiv d)).1
        (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h (I.toEquiv d)).2
    rw [he, hb b, ← kmswStage_eq_of_prefix w w' (t - 1) h]
  · intro b i
    have he : (fun z => (stageMapVertex w' (t - 1)
        (cutMapIsoVertexEquiv (I.trans J) z)).id) =
        (fun z => (stageMapVertex w (t - 1) (cutMapIsoVertexEquiv I z)).id) := by
      funext z
      exact stageVertexId_trans_prefix w w' (t - 1) h I z
    rw [he, ht b i]
    cases i <;> simp only [← kmswStage_eq_of_prefix w w' (t - 1) h]
  · have hid : ancestorPosDartId w' (t - 1) R hR (I.trans J) a z =
        ancestorPosDartId w (t - 1) R hR I a z := by
      exact Prod.ext
        (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h
          (I.toEquiv (ancestorPosDartMap R hR a z))).1
        (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h
          (I.toEquiv (ancestorPosDartMap R hR a z))).2
    exact hid.trans hzn

/-- Helper toward Lemma 5.5. Fixed-ID finite image certificates are measurable
finite-prefix events. The target is a permanent ID rather than a quotient label. -/
theorem measurableSet_finiteAncestorEdgeImage
    (x : XDP) (a : ThinMapSide) (s n t r : ℕ) (C : PositiveCutOutput) :
    MeasurableSet {w : ℕ → Fin 3 | finiteAncestorEdgeImage x a s n t r C w} := by
  refine measurableSet_of_factors_prefix (t - 1) _ ?_
  intro w w' h
  exact ⟨finiteAncestorEdgeImage_of_prefix x a s n t r C w w' h,
    finiteAncestorEdgeImage_of_prefix x a s n t r C w' w (fun i hi => (h i hi).symm)⟩

/-- Helper toward Lemma 5.5. At a good cut, the finite certificate event is
exactly membership in the geometric ancestor carrier, including level zero. -/
theorem geometricAncestorEdge_mem_iff_finiteImage
    (x : XDP) (q : Coherent x) (a : ThinMapSide) (s n k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2)) :
    n ∈ geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime a q s ↔
      finiteAncestorEdgeImage x a s n
        (selectedCutTime renewalTime (k + 1) q.1).toNat
        (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat
        (selectedCutPastCuts x renewalTime (k + 1) q.1) (W q) := by
  let t := (selectedCutTime renewalTime (k + 1) q.1).toNat
  let r := (-(q.1 t).2).toNat
  let F := fun {ℓ : ℕ} (R : KMSWMapRep ℓ r t)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap (W q) (t - 1))) =>
    fun z => (stageMapVertex (W q) (t - 1) (cutMapIsoVertexEquiv I z)).id
  have hrecord := selectedCut_past_boundary_target_record
    x renewalTime renewalTime_positiveSuccessTime q a k s hk
  have hidentify : ∀ (ℓ m : ℕ) (R : KMSWMapRep ℓ r t)
      (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap (W q) (t - 1)))
      (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
      (∀ b : ThinMapSide, (boundaryDarts R.B b).map
        (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
          (match b with
            | .left => (kmswStage (W q) (t - 1)).UL
            | .right => (kmswStage (W q) (t - 1)).LR).map (fun e => (e, false))) →
      (boundaryTarget R.B a s).map (F R I) =
        some (thinMapBoundaryVertex (W q) (HF x q) (HL x q) (HT x q) (HR x q) a s) →
      selectedCutPastCuts x renewalTime (k + 1) q.1 =
        (some ⟨m, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨r, ⟨m, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) →
      boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v →
      ancestorPosDartId (W q) (t - 1) R hR I a ''
        selectedDarts (presentation (ancestorPosHalfRep R hR a) a v) =
          {d : ℕ × Bool | d.1 ∈
            geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime a q s} := by
    intro ℓ m R hR I v hb htarget hc hv
    have hh := congrArg (Option.map (F R I)) (ancestorPos_boundaryTarget_map R hR a s)
    rw [hv, Option.map_some, htarget] at hh
    have hvid : ancestorPosVertexId (W q) (t - 1) R hR I a v =
        thinMapBoundaryVertex (W q) (HF x q) (HL x q) (HT x q) (HR x q) a s :=
      Option.some.inj hh
    have hp := sourceAncestorPosHalf_path_prefix
      x renewalTime renewalTime_positiveSuccessTime q s k hk R hR I hb hc
    have hseed (b : ThinMapSide) :
        AncestorPosHalfOffPrefixArcSeedIdentification
          (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I b := by
      apply ancestorPos_arcSeeds_of_boundaryLaunch
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp b
      apply (ancestorPos_boundaryLaunch_iff_seamLaunch
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp b).mpr
      apply (ancestorPos_seamLaunch_iff_argumentOrder
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp b).mpr
      exact fun i => ancestorPos_seamLaunch_argumentOrder
        (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp b i
    have hside := (ancestorPos_sideRanges_iff_arcSeeds
      (W q) (HF x q) (HL x q) (HT x q) (HR x q) (P x q) (t - 1) R hR I hp).mpr hseed
    have hg := sourceAncestorPosHalf_geometric_of_sideRange
      x renewalTime renewalTime_positiveSuccessTime q a s k hk R hR I v hvid hp (hside a)
    exact hg.1
  have htarget {ℓ : ℕ} (R : KMSWMapRep ℓ r t)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap (W q) (t - 1)))
      (ht : ∀ b i, (boundaryTarget R.B b i).map (F R I) =
        match i with
        | 0 => some 0
        | j + 1 => ((match b with
          | .left => (kmswStage (W q) (t - 1)).UL
          | .right => (kmswStage (W q) (t - 1)).LR)[j]?).map
            (kmswStage (W q) (t - 1)).east) :
      (boundaryTarget R.B a s).map (F R I) =
        some (thinMapBoundaryVertex (W q) (HF x q) (HL x q) (HT x q) (HR x q) a s) := by
    rw [ancestor_boundaryVertex_eq]
    cases s <;> exact (ht a _).trans hrecord
  constructor
  · intro hn
    obtain ⟨ℓ, m, R, hR, I, _, _, hb, ht, hc⟩ :=
      selectedCutPastCuts_representatives_boundary_stageIso
        x renewalTime renewalTime_positiveSuccessTime q k s hk
    have htg := htarget R I ht
    have hh := congrArg (Option.map (F R I)) (ancestorPos_boundaryTarget_map R hR a s)
    rw [htg, Option.map_map] at hh
    obtain ⟨v, hv, _⟩ := Option.map_eq_some_iff.mp hh
    refine ⟨ℓ, m, R, hR, I, v, hb, ht, hc, hv, ?_⟩
    rwa [hidentify ℓ m R hR I v hb htg hc hv]
  · rintro ⟨ℓ, m, R, hR, I, v, hb, ht, hc, hv, hn⟩
    rwa [hidentify ℓ m R hR I v hb (htarget R I ht) hc hv] at hn

/-- Helper toward Lemma 5.5. The finite certificate at each selected cut
is measurable on the coherent subtype, with its permanent edge IDs. -/
theorem measurable_finiteAncestorEdgeImage_at_cut
    (x : XDP) (a : ThinMapSide) (s n k : ℕ) :
    Measurable (fun q : Coherent x => decide (finiteAncestorEdgeImage x a s n
      (selectedCutTime renewalTime (k + 1) q.1).toNat
      (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat
      (selectedCutPastCuts x renewalTime (k + 1) q.1) (W q))) := by
  let G : (ℕ × ℕ × PositiveCutOutput) × (ℕ → Fin 3) → Bool := fun z =>
    decide (finiteAncestorEdgeImage x a s n z.1.1 z.1.2.1 z.1.2.2
      (boltzmannKMSWStream z.2))
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro z
    apply measurable_of_factors_prefix (z.1 + 1)
    intro c c' h
    apply Bool.decide_congr
    exact ⟨finiteAncestorEdgeImage_of_prefix x a s n z.1 z.2.1 z.2.2
        _ _ (fun i hi => h (i + 1) (by omega)),
      finiteAncestorEdgeImage_of_prefix x a s n z.1 z.2.1 z.2.2
        _ _ (fun i hi => (h (i + 1) (by omega)).symm)⟩
  have htime : Measurable (fun q : Coherent x =>
      (selectedCutTime renewalTime (k + 1) q.1).toNat) :=
    (measurable_of_countable ENat.toNat).comp
      ((measurable_selectedCutTime renewalTime (k + 1)
        renewalTime_positiveSuccessTime).comp measurable_subtype_coe)
  have heval : Measurable (fun q : Coherent x =>
      q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat) := by
    simpa only [selectedCutFuture, conditionedVectorShift, Nat.add_zero,
      Function.comp_def] using ((measurable_pi_apply 0).comp
        (measurable_selectedCutFuture renewalTime (k + 1)
          renewalTime_positiveSuccessTime)).comp measurable_subtype_coe
  have hr : Measurable (fun q : Coherent x =>
      (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat) :=
    (measurable_of_countable (fun j : ℤ => (-j).toNat)).comp heval.snd
  exact hG.comp ((htime.prodMk (hr.prodMk
    ((measurable_selectedCutPastCuts x renewalTime (k + 1)
      renewalTime_positiveSuccessTime).comp measurable_subtype_coe))).prodMk
        (measurable_pathCode.comp measurable_subtype_coe))

/-- Helper toward Lemma 5.5. Membership of a fixed permanent edge ID in
one geometric ancestor level is measurable on the coherent subtype. -/
theorem measurableSet_geometricAncestorEdges
    (x : XDP) (a : ThinMapSide) (s n : ℕ) :
    MeasurableSet {q : Coherent x | n ∈ geometricAncestorEdges
      x renewalTime renewalTime_positiveSuccessTime a q s} := by
  have hG : Measurable (fun z : ℕ × Coherent x =>
      decide (finiteAncestorEdgeImage x a s n
        (selectedCutTime renewalTime (z.1 + 1) z.2.1).toNat
        (-(z.2.1 (selectedCutTime renewalTime (z.1 + 1) z.2.1).toNat).2).toNat
        (selectedCutPastCuts x renewalTime (z.1 + 1) z.2.1) (W z.2))) :=
    measurable_from_prod_countable_right
      (measurable_finiteAncestorEdgeImage_at_cut x a s n)
  have h := hG.comp ((measurable_leastGoodCut x renewalTime
    renewalTime_positiveSuccessTime s).prodMk measurable_id)
  have he : (fun q : Coherent x => decide (n ∈ geometricAncestorEdges
      x renewalTime renewalTime_positiveSuccessTime a q s)) =
      (fun q : Coherent x => decide (finiteAncestorEdgeImage x a s n
        (selectedCutTime renewalTime
          (leastGoodCut x renewalTime renewalTime_positiveSuccessTime s q + 1) q.1).toNat
        (-(q.1 (selectedCutTime renewalTime
          (leastGoodCut x renewalTime renewalTime_positiveSuccessTime s q + 1) q.1).toNat).2).toNat
        (selectedCutPastCuts x renewalTime
          (leastGoodCut x renewalTime renewalTime_positiveSuccessTime s q + 1) q.1) (W q))) := by
    funext q
    exact Bool.decide_congr (geometricAncestorEdge_mem_iff_finiteImage x q a s n _
      (leastGoodCut_spec x renewalTime renewalTime_positiveSuccessTime s q))
  have hm : Measurable (fun q : Coherent x => decide (n ∈ geometricAncestorEdges
      x renewalTime renewalTime_positiveSuccessTime a q s)) := he.symm ▸ h
  have hh := hm (measurableSet_singleton true)
  change MeasurableSet {q : Coherent x | decide (n ∈ geometricAncestorEdges
    x renewalTime renewalTime_positiveSuccessTime a q s) = true} at hh
  simpa only [decide_eq_true_eq] using hh

/-- Helper toward Lemma 5.5. Fixed-ID membership at a right ancestor level
is a measurable event. -/
theorem measurableSet_geometricRightAncestorEdges
    (x : XDP) (s n : ℕ) :
    MeasurableSet {q : Coherent x | n ∈ geometricAncestorEdges
      x renewalTime renewalTime_positiveSuccessTime .right q s} :=
  measurableSet_geometricAncestorEdges x .right s n

/-- Helper toward Lemma 5.5. The full right edge carrier is the countable
union of its measurable geometric ancestor levels. -/
theorem measurable_geometricRightSide_edges (x : XDP) (n : ℕ) :
    Measurable (fun q : Coherent x => decide (n ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges)) := by
  have hm : MeasurableSet {q : Coherent x | n ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges} := by
    change MeasurableSet {q : Coherent x | n ∈ ⋃ s,
      geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime .right q s}
    simp only [Set.mem_iUnion]
    simpa only [Set.iUnion_ofPred] using
      MeasurableSet.iUnion (fun s => measurableSet_geometricRightAncestorEdges x s n)
  have he : (fun q : Coherent x => decide (n ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges)) =
      (fun q : Coherent x => if n ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges
        then true else false) := by
    funext q
    split <;> simp_all only [decide_true, decide_false]
  rw [he]
  exact measurable_const.ite hm measurable_const


/-- Helper toward Lemma 5.5. A stage rotation entry, extended by a fixed dart
before its input edge has been allocated. -/
@[expose] noncomputable def finiteRotationEntry (w : ℕ → Fin 3) (t : ℕ)
    (d : ℕ × Bool) : ℕ × Bool :=
  if hd : d.1 < (kmswStage w t).nextEdge then
    let e := stageRot w t (⟨d.1, hd⟩, d.2)
    (e.1.val, e.2)
  else (0, false)

/-- Helper toward Lemma 5.5. Stage rotation entries retain their permanent
dart IDs under prefix transport. -/
theorem finiteRotationEntry_of_prefix (w w' : ℕ → Fin 3) (t : ℕ)
    (h : ∀ i < t, w i = w' i) (d : ℕ × Bool) :
    finiteRotationEntry w t d = finiteRotationEntry w' t d := by
  have hs := kmswStage_eq_of_prefix w w' t h
  by_cases hd : d.1 < (kmswStage w t).nextEdge
  · have hd' : d.1 < (kmswStage w' t).nextEdge := by rwa [← hs]
    let J := kmswStageDirectedMapIsoOfPrefix w w' t h
    let e : StageDart (kmswStage w t).nextEdge := (⟨d.1, hd⟩, d.2)
    have he : J.toEquiv e = (⟨d.1, hd'⟩, d.2) := by
      apply Prod.ext
      · apply Fin.ext
        exact (kmswStageDirectedMapIsoOfPrefix_val w w' t h e).1
      · exact (kmswStageDirectedMapIsoOfPrefix_val w w' t h e).2
    have hr := congrArg (fun z : StageDart (kmswStage w' t).nextEdge => (z.1.val, z.2))
      (J.rot_comm e)
    change ((J.toEquiv (stageRot w t e)).1.val, (J.toEquiv (stageRot w t e)).2) =
      ((stageRot w' t (J.toEquiv e)).1.val, (stageRot w' t (J.toEquiv e)).2) at hr
    rw [(kmswStageDirectedMapIsoOfPrefix_val w w' t h (stageRot w t e)).1,
      (kmswStageDirectedMapIsoOfPrefix_val w w' t h (stageRot w t e)).2, he] at hr
    simpa only [finiteRotationEntry, dite_eq_left hd, dite_eq_left hd', e] using hr
  · have hd' : ¬ d.1 < (kmswStage w' t).nextEdge := by rwa [← hs]
    simp only [finiteRotationEntry, dite_eq_right hd, dite_eq_right hd']

/-- Helper toward Lemma 5.5. A fixed limiting rotation entry is measurable:
its fibres are countable unions of countable intersections of stage fibres. -/
theorem measurable_coherentRotation (x : XDP) (d : ℕ × Bool) :
    Measurable (fun q : Coherent x => kmswInfRot (W q) (HF x q) d) := by
  have hstage (t : ℕ) : Measurable (fun q : Coherent x =>
      finiteRotationEntry (W q) t d) := by
    refine (measurable_of_factors_prefix (t + 1)
      (fun c => finiteRotationEntry (boltzmannKMSWStream c) t d) ?_).comp
        (measurable_pathCode.comp measurable_subtype_coe)
    intro c c' h
    exact finiteRotationEntry_of_prefix _ _ t (fun i hi => h (i + 1) (by omega)) d
  have hstab (q : Coherent x) : ∃ N, ∀ t ≥ N,
      kmswInfRot (W q) (HF x q) d = finiteRotationEntry (W q) t d := by
    obtain ⟨N, hN⟩ := kmswInfRot_eventually_eq_stage (W q) (HF x q) d
    refine ⟨N, fun t ht => ?_⟩
    obtain ⟨hd, hh⟩ := hN t ht
    simpa only [finiteRotationEntry, dite_eq_left hd] using hh
  apply measurable_to_countable'
  intro e
  have he : {q : Coherent x | kmswInfRot (W q) (HF x q) d = e} =
      ⋃ N : ℕ, ⋂ t : ℕ, ⋂ (_ : N ≤ t),
        {q : Coherent x | finiteRotationEntry (W q) t d = e} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    obtain ⟨M, hM⟩ := hstab q
    constructor
    · intro hh
      exact ⟨M, fun t ht => (hM t ht).symm.trans hh⟩
    · rintro ⟨N, hN⟩
      exact (hM (max M N) (le_max_left M N)).trans
        (hN (max M N) (le_max_right M N))
  change MeasurableSet {q : Coherent x | kmswInfRot (W q) (HF x q) d = e}
  rw [he]
  exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun t =>
    MeasurableSet.iInter (fun _ => measurableSet_eq_fun (hstage t) measurable_const)))

/-- Helper toward Lemma 5.5. Every finite iterate of the limiting rotation
is measurable, including its permanent dart ID. -/
theorem measurable_coherentRotation_iterate (x : XDP) (d : ℕ × Bool) (k : ℕ) :
    Measurable (fun q : Coherent x =>
      (kmswInfRot (W q) (HF x q) : (ℕ × Bool) → ℕ × Bool)^[k] d) := by
  have hG : Measurable (fun z : (ℕ × Bool) × Coherent x =>
      kmswInfRot (W z.2) (HF x z.2) z.1) :=
    measurable_from_prod_countable_right (measurable_coherentRotation x)
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simpa only [Function.iterate_succ_apply', Function.comp_def, id_eq] using
      hG.comp (ih.prodMk measurable_id)

/-- Helper toward Lemma 5.5. Induced rotation on the right side is measurable
by the countable first-return formula on its complete edge carrier. -/
theorem measurable_geometricRightSide_rotation (x : XDP) (d e : ℕ × Bool) :
    Measurable (fun q : Coherent x => decide ((geometricSideSubmap
      x renewalTime renewalTime_positiveSuccessTime .right q).rotation d e)) := by
  have hedge (j : ℕ) : Measurable (fun q : Coherent x => decide
      (((kmswInfRot (W q) (HF x q) : (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges)) := by
    have hG : Measurable (fun z : ℕ × Coherent x => decide (z.1 ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.2).edges)) :=
      measurable_from_prod_countable_right (measurable_geometricRightSide_edges x)
    have hcomp := hG.comp
      ((measurable_coherentRotation_iterate x d j).fst.prodMk measurable_id)
    simpa only [Function.comp_def, id_eq] using hcomp
  have hm : MeasurableSet {q : Coherent x | ∃ k : ℕ, 0 < k ∧
      (kmswInfRot (W q) (HF x q) : (ℕ × Bool) → ℕ × Bool)^[k] d = e ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswInfRot (W q) (HF x q) : (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∉
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges} := by
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro k
    rw [Set.ofPred_and]
    apply (MeasurableSet.const (0 < k)).inter
    rw [Set.ofPred_and]
    apply (measurableSet_eq_fun (measurable_coherentRotation_iterate x d k) measurable_const).inter
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.imp (MeasurableSet.const (0 < j))
    apply MeasurableSet.imp (MeasurableSet.const (j < k))
    have hh := hedge j (measurableSet_singleton false)
    change MeasurableSet {q : Coherent x | decide
      (((kmswInfRot (W q) (HF x q) : (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges) = false} at hh
    simpa only [decide_eq_false_iff_not] using hh
  have he : (fun q : Coherent x => decide ((geometricSideSubmap
      x renewalTime renewalTime_positiveSuccessTime .right q).rotation d e)) =
      (fun q : Coherent x => if (geometricSideSubmap
        x renewalTime renewalTime_positiveSuccessTime .right q).rotation d e
        then true else false) := by
    funext q
    split <;> simp_all only [decide_true, decide_false]
  rw [he]
  exact measurable_const.ite hm measurable_const

/-- Helper toward Lemma 5.5. Limiting face succession is measurable through
the inverse of the measurable permutation of permanent darts. -/
theorem measurable_coherentFaceSucc (x : XDP) (d : ℕ × Bool) :
    Measurable (fun q : Coherent x => kmswInfFaceSucc (W q) (HF x q) d) := by
  apply measurable_to_countable'
  intro e
  change MeasurableSet {q : Coherent x | kmswInfFaceSucc (W q) (HF x q) d = e}
  have he : {q : Coherent x | kmswInfFaceSucc (W q) (HF x q) d = e} =
      {q : Coherent x | kmswInfRot (W q) (HF x q) e = (d.1, !d.2)} := by
    ext q
    change (kmswInfRot (W q) (HF x q)).symm (d.1, !d.2) = e ↔ _
    change (kmswInfRot (W q) (HF x q)).symm (d.1, !d.2) = e ↔
      kmswInfRot (W q) (HF x q) e = (d.1, !d.2)
    rw [Equiv.symm_apply_eq]
    exact eq_comm
  rw [he]
  exact measurableSet_eq_fun (measurable_coherentRotation x e) measurable_const

/-- Helper toward Lemma 5.5. A creation-time triangle with its literal
permanent dart list is a finite-prefix event. -/
theorem measurableSet_coherentTriangleList
    (x : XDP) (j : ℕ) (l : List (ℕ × Bool)) :
    MeasurableSet {q : Coherent x | ∃ h : (W q) j = 0 ∨ (W q) j = 1,
      stageTriangleDartList (W q) ⟨j, h⟩ = l} := by
  refine (measurableSet_of_factors_prefix (j + 2)
    (fun c => ∃ h : (boltzmannKMSWStream c) j = 0 ∨ (boltzmannKMSWStream c) j = 1,
      stageTriangleDartList (boltzmannKMSWStream c) ⟨j, h⟩ = l) ?_).preimage
        (measurable_pathCode.comp measurable_subtype_coe)
  intro c c' h
  have hc : (boltzmannKMSWStream c) j = (boltzmannKMSWStream c') j :=
    h (j + 1) (by omega)
  have hs : kmswStage (boltzmannKMSWStream c) j =
      kmswStage (boltzmannKMSWStream c') j :=
    kmswStage_congr (fun i hi => h (i + 1) (by omega))
  constructor
  · rintro ⟨hj, hl⟩
    refine ⟨hc ▸ hj, ?_⟩
    simpa only [stageTriangleDartList, stageTriangleDartTriple, hs, hc] using hl
  · rintro ⟨hj, hl⟩
    refine ⟨hc.symm ▸ hj, ?_⟩
    simpa only [stageTriangleDartList, stageTriangleDartTriple, hs, hc] using hl

/-- Helper toward Lemma 5.5. Retained right-side faces keep their original
triangle succession; every condition is a measurable countable-coordinate event. -/
theorem measurable_geometricRightSide_faceNext (x : XDP) (d e : ℕ × Bool) :
    Measurable (fun q : Coherent x => decide ((geometricSideSubmap
      x renewalTime renewalTime_positiveSuccessTime .right q).faceNext d e)) := by
  have hedges (l : List (ℕ × Bool)) : MeasurableSet {q : Coherent x |
      ∀ z ∈ l, z.1 ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro z
    apply MeasurableSet.imp (MeasurableSet.const (z ∈ l))
    have hh := measurable_geometricRightSide_edges x z.1 (measurableSet_singleton true)
    change MeasurableSet {q : Coherent x | decide (z.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges) = true} at hh
    simpa only [decide_eq_true_eq] using hh
  have hm : MeasurableSet {q : Coherent x | ∃ (j : ℕ) (l : List (ℕ × Bool)),
      (∃ h : (W q) j = 0 ∨ (W q) j = 1, stageTriangleDartList (W q) ⟨j, h⟩ = l) ∧
      d ∈ l ∧ ∀ z ∈ l, z.1 ∈
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges} := by
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro l
    rw [Set.ofPred_and, Set.ofPred_and]
    exact (measurableSet_coherentTriangleList x j l).inter
      ((MeasurableSet.const (d ∈ l)).inter (hedges l))
  have he : {q : Coherent x | (geometricSideSubmap
      x renewalTime renewalTime_positiveSuccessTime .right q).faceNext d e} =
      {q : Coherent x | ∃ (j : ℕ) (l : List (ℕ × Bool)),
        (∃ h : (W q) j = 0 ∨ (W q) j = 1, stageTriangleDartList (W q) ⟨j, h⟩ = l) ∧
        d ∈ l ∧ ∀ z ∈ l, z.1 ∈
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges} ∩
        {q : Coherent x | kmswInfFaceSucc (W q) (HF x q) d = e} := by
    ext q
    constructor
    · rintro ⟨⟨j, hd, hall⟩, he⟩
      exact ⟨⟨j.1, stageTriangleDartList (W q) j, ⟨j.2, rfl⟩, hd, hall⟩, he⟩
    · rintro ⟨⟨j, l, ⟨hj, hl⟩, hd, hall⟩, he⟩
      subst l
      exact ⟨⟨⟨j, hj⟩, hd, hall⟩, he⟩
  have hface : MeasurableSet {q : Coherent x | (geometricSideSubmap
      x renewalTime renewalTime_positiveSuccessTime .right q).faceNext d e} := by
    rw [he]
    exact hm.inter (measurableSet_eq_fun (measurable_coherentFaceSucc x d) measurable_const)
  have heq : (fun q : Coherent x => decide ((geometricSideSubmap
      x renewalTime renewalTime_positiveSuccessTime .right q).faceNext d e)) =
      (fun q : Coherent x => if (geometricSideSubmap
        x renewalTime renewalTime_positiveSuccessTime .right q).faceNext d e
        then true else false) := by
    funext q
    split <;> simp_all only [decide_true, decide_false]
  rw [heq]
  exact measurable_const.ite hface measurable_const

/-- Helper toward Lemma 5.5. A finite certificate retains its boundary lists,
the actual selected cut classes and an indexed permanent seam edge ID. -/
@[expose] noncomputable def finiteSeamEntry
    (x : XDP) (_a : ThinMapSide) (s n t r : ℕ) (C : PositiveCutOutput)
    (w : ℕ → Fin 3) : Prop :=
  ∃ (ℓ m : ℕ) (R : KMSWMapRep ℓ r t) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1))),
    (∀ b : ThinMapSide, (boundaryDarts R.B b).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match b with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false))) ∧
    C =
      (some ⟨m, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
       some ⟨r, ⟨m, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) ∧
    (((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val))[s]? = some n

/-- Helper toward Lemma 5.5. A finite seam certificate transports along a
common code prefix without changing any permanent seam edge ID. -/
theorem finiteSeamEntry_of_prefix
    (x : XDP) (a : ThinMapSide) (s n t r : ℕ) (C : PositiveCutOutput)
    (w w' : ℕ → Fin 3) (h : ∀ i < t - 1, w i = w' i) :
    finiteSeamEntry x a s n t r C w →
      finiteSeamEntry x a s n t r C w' := by
  rintro ⟨ℓ, m, R, hR, I, hb, hc, hentry⟩
  let J := kmswStageDirectedMapIsoOfPrefix w w' (t - 1) h
  refine ⟨ℓ, m, R, hR, I.trans J, ?_, hc, ?_⟩
  · intro b
    have he : (fun d => (((I.trans J).toEquiv d).1.val,
        ((I.trans J).toEquiv d).2)) =
        (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) := by
      funext d
      exact Prod.ext
        (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h (I.toEquiv d)).1
        (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h (I.toEquiv d)).2
    rw [he, hb b, ← kmswStage_eq_of_prefix w w' (t - 1) h]
  · have he : (fun d => (((I.trans J).toEquiv d).1.val)) =
        (fun d => ((I.toEquiv d).1.val)) := by
      funext d
      exact (kmswStageDirectedMapIsoOfPrefix_val w w' (t - 1) h (I.toEquiv d)).1
    simpa only [List.map_map, Function.comp_def, he] using hentry


/-- Helper toward Lemma 5.5. The finite certificate at each selected cut
is measurable on the coherent subtype, with its permanent seam edge IDs. -/
theorem measurable_finiteSeamEntry_at_cut
    (x : XDP) (a : ThinMapSide) (s n k : ℕ) :
    Measurable (fun q : Coherent x => decide (finiteSeamEntry x a s n
      (selectedCutTime renewalTime (k + 1) q.1).toNat
      (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat
      (selectedCutPastCuts x renewalTime (k + 1) q.1) (W q))) := by
  let G : (ℕ × ℕ × PositiveCutOutput) × (ℕ → Fin 3) → Bool := fun z =>
    decide (finiteSeamEntry x a s n z.1.1 z.1.2.1 z.1.2.2
      (boltzmannKMSWStream z.2))
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro z
    apply measurable_of_factors_prefix (z.1 + 1)
    intro c c' h
    apply Bool.decide_congr
    exact ⟨finiteSeamEntry_of_prefix x a s n z.1 z.2.1 z.2.2
        _ _ (fun i hi => h (i + 1) (by omega)),
      finiteSeamEntry_of_prefix x a s n z.1 z.2.1 z.2.2
        _ _ (fun i hi => (h (i + 1) (by omega)).symm)⟩
  have htime : Measurable (fun q : Coherent x =>
      (selectedCutTime renewalTime (k + 1) q.1).toNat) :=
    (measurable_of_countable ENat.toNat).comp
      ((measurable_selectedCutTime renewalTime (k + 1)
        renewalTime_positiveSuccessTime).comp measurable_subtype_coe)
  have heval : Measurable (fun q : Coherent x =>
      q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat) := by
    simpa only [selectedCutFuture, conditionedVectorShift, Nat.add_zero,
      Function.comp_def] using ((measurable_pi_apply 0).comp
        (measurable_selectedCutFuture renewalTime (k + 1)
          renewalTime_positiveSuccessTime)).comp measurable_subtype_coe
  have hr : Measurable (fun q : Coherent x =>
      (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat) :=
    (measurable_of_countable (fun j : ℤ => (-j).toNat)).comp heval.snd
  exact hG.comp ((htime.prodMk (hr.prodMk
    ((measurable_selectedCutPastCuts x renewalTime (k + 1)
      renewalTime_positiveSuccessTime).comp measurable_subtype_coe))).prodMk
        (measurable_pathCode.comp measurable_subtype_coe))


/-- Helper toward Lemma 5.5. Every indexed infinite seam edge is read in a
sufficiently large good-cut certificate, and every such reading is exact. -/
theorem sourceAncestorPath_edge_iff_finiteSeam
    (x : XDP) (q : Coherent x) (i n : ℕ) :
    (P x q).edge i = n ↔ ∃ k : ℕ,
      (1 : ℤ) ≤ min ((q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2) ∧
      finiteSeamEntry x .right i n
        (selectedCutTime renewalTime (k + 1) q.1).toNat
        (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat
        (selectedCutPastCuts x renewalTime (k + 1) q.1) (W q) := by
  constructor
  · intro hn
    let s := (P x q).edge i
    let k := leastGoodCut x renewalTime renewalTime_positiveSuccessTime s q
    have hk := leastGoodCut_spec x renewalTime renewalTime_positiveSuccessTime s q
    obtain ⟨ℓ, m, R, hR, I, _, _, hb, _, hc⟩ :=
      selectedCutPastCuts_representatives_boundary_stageIso
        x renewalTime renewalTime_positiveSuccessTime q k s hk
    have hp := sourceAncestorPosHalf_path_prefix
      x renewalTime renewalTime_positiveSuccessTime q s k hk R hR I hb hc
    have hbefore := (selectedCut_boundary_indices_before
      x renewalTime renewalTime_positiveSuccessTime q k s hk).2.1
    have hcount := (natSelect_spec (right_record_infinite (W q) (HR x q)) s).2
    have hle := Nat.count_le (p := fun m => ∀ j, j < m →
        DirectedDistances.KMSW.R (W q) m < DirectedDistances.KMSW.R (W q) j)
      (n := natSelect (fun m => ∀ j, j < m →
        DirectedDistances.KMSW.R (W q) m < DirectedDistances.KMSW.R (W q) j) s)
    rw [hcount] at hle
    have halloc : s < (kmswStage (W q)
        ((selectedCutTime renewalTime (k + 1) q.1).toNat - 1)).nextEdge :=
      kmsw_nextEdge_unbounded (W q) s _ (by omega)
    have hi := ancestorPos_seam_index_lt_of_allocated (W q)
      ((selectedCutTime renewalTime (k + 1) q.1).toNat - 1) R hR I (P x q) hp i halloc
    refine ⟨k, (show (1 : ℤ) ≤ (s : ℤ) + 1 by omega).trans hk,
      ℓ, m, R, hR, I, hb, hc, ?_⟩
    rw [hp]
    simp only [List.getElem?_ofFn, dite_eq_left hi, hn]
  · rintro ⟨k, hk, ℓ, m, R, hR, I, hb, hc, hentry⟩
    have hp := sourceAncestorPosHalf_path_prefix x renewalTime renewalTime_positiveSuccessTime
      q 0 k (by simpa using hk) R hR I hb hc
    rw [hp] at hentry
    by_cases hi : i < m
    · simpa only [List.getElem?_ofFn, dite_eq_left hi, Option.some.injEq] using hentry
    · simp only [List.getElem?_ofFn, dite_eq_right hi] at hentry
      cases hentry

/-- Helper toward Lemma 5.5. Each permanent seam edge coordinate is measurable
as a countable union of exact finite readings at good cuts. -/
theorem measurable_geometricRightSide_seam (x : XDP) (i : ℕ) :
    Measurable (fun q : Coherent x => (geometricSideSubmap
      x renewalTime renewalTime_positiveSuccessTime .right q).seam i) := by
  have hm : Measurable (fun q : Coherent x => (P x q).edge i) := by
    apply measurable_to_countable'
    intro n
    change MeasurableSet {q : Coherent x | (P x q).edge i = n}
    have he : {q : Coherent x | (P x q).edge i = n} = ⋃ k : ℕ,
        {q : Coherent x | (1 : ℤ) ≤
          min ((q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).1)
            (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2)} ∩
        {q : Coherent x | finiteSeamEntry x .right i n
          (selectedCutTime renewalTime (k + 1) q.1).toNat
          (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat
          (selectedCutPastCuts x renewalTime (k + 1) q.1) (W q)} := by
      ext q
      simpa only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff] using
        sourceAncestorPath_edge_iff_finiteSeam x q i n
    rw [he]
    apply MeasurableSet.iUnion
    intro k
    apply ((measurableSet_selectedCutTime_good_event renewalTime
      renewalTime_positiveSuccessTime 0 (k + 1)).preimage measurable_subtype_coe).inter
    have hh := measurable_finiteSeamEntry_at_cut x .right i n k (measurableSet_singleton true)
    change MeasurableSet {q : Coherent x | decide (finiteSeamEntry x .right i n
      (selectedCutTime renewalTime (k + 1) q.1).toNat
      (-(q.1 (selectedCutTime renewalTime (k + 1) q.1).toNat).2).toNat
      (selectedCutPastCuts x renewalTime (k + 1) q.1) (W q)) = true} at hh
    simpa only [decide_eq_true_eq] using hh
  exact hm.prodMk measurable_const

/-- Helper toward Lemma 5.5. All ten permanent-ID fields of the coherent
geometric right side are jointly measurable. -/
theorem measurable_geometricRightSide (x : XDP) :
    Measurable (fun q : Coherent x =>
      geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun q : Coherent x => geometricSideCode
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q))
  exact (measurable_pi_iff.mpr (measurable_geometricRightSide_vertices x)).prodMk
    ((measurable_pi_iff.mpr (measurable_geometricRightSide_edges x)).prodMk
      ((measurable_pi_iff.mpr (measurable_geometricRightSide_west x)).prodMk
        ((measurable_pi_iff.mpr (measurable_geometricRightSide_east x)).prodMk
          ((measurable_pi_iff.mpr (measurable_geometricRightSide_present x)).prodMk
            ((measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr
              (measurable_geometricRightSide_rotation x d))).prodMk
              ((measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr
                (measurable_geometricRightSide_faceNext x d))).prodMk
                ((measurable_geometricRightSide_root x).prodMk
                  ((measurable_pi_iff.mpr (measurable_geometricRightSide_boundary x)).prodMk
                    (measurable_pi_iff.mpr (measurable_geometricRightSide_seam x))))))))))

/-- Helper toward Lemma 5.5. The marked-isomorphism class of the complete
coherent geometric right side is measurable. -/
theorem measurable_geometricRightSide_class (x : XDP) :
    Measurable (fun q : Coherent x => geometricSideClass
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :=
  measurable_geometricSideClass.comp (measurable_geometricRightSide x)

/-- Helper toward Lemma 5.5. The optional right-side class has the same law
at every nonnegative boundary index, using the complete hatted path law.
Precisely the incoherent inputs return `none`; no fallback side is introduced. -/
theorem geometricRightSide_class_law_eq_zero
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    let F : (ℕ → ℤ × ℤ) → Option GeometricSideClass := fun p =>
      if hp : p ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime
      then some (geometricSideClass
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right ⟨p, hp⟩))
      else none
    wholePlaneIIDCodeMeasure.map (fun ω => F (boundaryFutureHattedPath k ω)) =
      wholePlaneIIDCodeMeasure.map (fun ω => F (boundaryFutureHattedPath 0 ω)) := by
  intro F
  have hF : Measurable F :=
    (measurable_some_geometricSideClass.comp (measurable_geometricRightSide_class x)).dite
      measurable_const
      (selectedCutCoherentDomain_measurable_conull x renewalTime renewalTime_positiveSuccessTime).1
  change wholePlaneIIDCodeMeasure.map (F ∘ boundaryFutureHattedPath k) =
    wholePlaneIIDCodeMeasure.map (F ∘ boundaryFutureHattedPath 0)
  rw [← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable
      (aemeasurable_boundaryFutureHattedPath k),
    ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable
      (aemeasurable_boundaryFutureHattedPath 0),
    boundaryFutureHattedPath_map_law k, boundaryFutureHattedPath_map_law 0]

end DirectedDistances.PaperProofs.Section5
