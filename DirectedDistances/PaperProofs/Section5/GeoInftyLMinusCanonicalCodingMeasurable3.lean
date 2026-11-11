/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusCanonicalCodingMeasurable2

/-! Measurable relation coordinates on certified coherent presentation/path pairs.
Presentation-only descent is a separate obligation. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. Limiting primed rotation coordinates are
measurable on the certified domain by eventual finite-stage stabilization. -/
theorem measurable_lMinusCanonicalCodingDomain_primedRotation (x : XDP)
    (d : ℕ × Bool) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      kmswInfRot z.val.1.code.1 z.property d) := by
  have hstage (t : ℕ) : Measurable (fun z : LMinusCanonicalCodingDomain x =>
      finiteRotationEntry z.val.1.code.1 t d) := by
    exact (measurable_of_factors_prefix t (fun p => finiteRotationEntry p t d)
      (fun p p' hp => finiteRotationEntry_of_prefix p p' t hp d)).comp
        (((measurable_lMinusSidePresentation_code x).fst.comp measurable_fst).comp
          measurable_subtype_coe)
  have hstab (z : LMinusCanonicalCodingDomain x) : ∃ N, ∀ t ≥ N,
      kmswInfRot z.val.1.code.1 z.property d =
        finiteRotationEntry z.val.1.code.1 t d := by
    obtain ⟨N, hN⟩ := kmswInfRot_eventually_eq_stage z.val.1.code.1 z.property d
    refine ⟨N, fun t ht => ?_⟩
    obtain ⟨hd, hh⟩ := hN t ht
    simpa only [finiteRotationEntry, dite_eq_left hd] using hh
  apply measurable_to_countable'
  intro e
  change MeasurableSet {z : LMinusCanonicalCodingDomain x |
    kmswInfRot z.val.1.code.1 z.property d = e}
  have he : {z : LMinusCanonicalCodingDomain x |
      kmswInfRot z.val.1.code.1 z.property d = e} =
      ⋃ N : ℕ, ⋂ t : ℕ, ⋂ (_ : N ≤ t),
        {z | finiteRotationEntry z.val.1.code.1 t d = e} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    obtain ⟨M, hM⟩ := hstab z
    constructor
    · intro h
      exact ⟨M, fun t ht => (hM t ht).symm.trans h⟩
    · rintro ⟨N, hN⟩
      exact (hM (max M N) (le_max_left M N)).trans
        (hN (max M N) (le_max_right M N))
  rw [he]
  exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun t =>
    MeasurableSet.iInter (fun _ => ((hstage t).eq_const e).setOf)))

/-- Helper toward Lemma 5.5. Primed face successors are measurable by
inverting the measurable limiting rotation on the countable dart carrier. -/
theorem measurable_lMinusCanonicalCodingDomain_primedFaceSucc (x : XDP)
    (d : ℕ × Bool) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      kmswInfFaceSucc z.val.1.code.1 z.property d) := by
  apply measurable_to_countable'
  intro e
  change MeasurableSet {z : LMinusCanonicalCodingDomain x |
    kmswInfFaceSucc z.val.1.code.1 z.property d = e}
  have he : {z : LMinusCanonicalCodingDomain x |
      kmswInfFaceSucc z.val.1.code.1 z.property d = e} =
      {z | kmswInfRot z.val.1.code.1 z.property e = (d.1, !d.2)} := by
    ext z
    change (kmswInfRot z.val.1.code.1 z.property).symm (d.1, !d.2) = e ↔ _
    rw [Equiv.symm_apply_eq]
    exact eq_comm
  rw [he]
  exact ((measurable_lMinusCanonicalCodingDomain_primedRotation x e).eq_const _).setOf

/-- Helper toward Lemma 5.5. Canonical IDs of fixed primed darts retain
the measurable boundary orientation correction. -/
theorem measurable_lMinusCanonicalPrimedDartId (x : XDP) (d : ℕ × Bool) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2)
        (lMinusCodePrimedDart z.val.1 _ d)) := by
  have he := (measurable_lMinusCoherentEdgeId x (.inl d.1)).comp
    (measurable_subtype_coe (p := fun z : LMinusSidePresentation x × Coherent x =>
      KMSWFiniteIncidence z.1.code.1))
  have hb := (measurable_of_finite (fun b : Bool => d.2 ^^ b)).comp
    ((measurable_lMinusCodePrimedSideFlip x d.1).comp
      (measurable_fst.comp (measurable_subtype_coe (p := fun z : LMinusSidePresentation x × Coherent x => KMSWFiniteIncidence z.1.code.1))))
  convert he.prodMk hb using 1
  funext z
  exact Prod.ext (lMinusCoherentEdgeId_eq z.val.1 z.val.2 (.inl d.1)).symm rfl

/-- Helper toward Lemma 5.5. Canonical IDs of fixed ambient hatted darts
are measurable before restricting to their geometric carrier. -/
theorem measurable_lMinusCanonicalHattedRawDartId (x : XDP) (d : ℕ × Bool) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      (lMinusCoherentEdgeId z.val (.inr d.1), d.2)) :=
  ((measurable_lMinusCoherentEdgeId x (.inr d.1)).comp
    measurable_subtype_coe).prodMk measurable_const

/-- Helper toward Lemma 5.5. The measurable raw hatted dart ID agrees
with the intrinsic canonical ID on every allocated geometric dart. -/
theorem lMinusCanonicalHattedRawDartId_eq (x : XDP)
    (z : LMinusCanonicalCodingDomain x)
    (d : {d : ℕ × Bool // d.1 ∈ (lMinusCoherentLeftSide x z.val.2).edges}) :
    (lMinusCoherentEdgeId z.val (.inr d.val.1), d.val.2) =
      lMinusCanonicalDartId z.val.1 _ (lMinusCodeHattedDart z.val.1 _ d) :=
  Prod.ext (lMinusCoherentEdgeId_eq z.val.1 z.val.2 (.inr ⟨d.val.1, d.property⟩)) rfl

/-- Helper toward Lemma 5.5. Membership of a fixed primed dart in a
creation triangle is a countable union of finite-prefix events. -/
theorem measurableSet_lMinusPrimedTriangleDart (x : XDP) (d : ℕ × Bool) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      ∃ j : TriangleCreationTime z.val.1.code.1,
        d ∈ stageTriangleDartList z.val.1.code.1 j} := by
  have hj (j : ℕ) : MeasurableSet {p : ℕ → Fin 3 |
      ∃ h : p j = 0 ∨ p j = 1, d ∈ stageTriangleDartList p ⟨j, h⟩} := by
    apply measurableSet_of_factors_prefix (j + 1)
    intro p p' hp
    have hc := hp j (Nat.lt_succ_self j)
    have hs : kmswStage p j = kmswStage p' j := kmswStage_congr (fun i hi => hp i (by omega : i < j + 1))
    constructor
    · rintro ⟨h, hd⟩
      refine ⟨hc ▸ h, ?_⟩
      simpa only [stageTriangleDartList, stageTriangleDartTriple, hs, hc] using hd
    · rintro ⟨h, hd⟩
      refine ⟨hc.symm ▸ h, ?_⟩
      simpa only [stageTriangleDartList, stageTriangleDartTriple, hs, hc] using hd
  have he : {z : LMinusCanonicalCodingDomain x |
      ∃ j : TriangleCreationTime z.val.1.code.1,
        d ∈ stageTriangleDartList z.val.1.code.1 j} =
      ⋃ j : ℕ, {z | ∃ h : z.val.1.code.1 j = 0 ∨ z.val.1.code.1 j = 1,
        d ∈ stageTriangleDartList z.val.1.code.1 ⟨j, h⟩} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨⟨j, h⟩, hd⟩ => ⟨j, h, hd⟩,
      fun ⟨j, h, hd⟩ => ⟨⟨j, h⟩, hd⟩⟩
  rw [he]
  exact MeasurableSet.iUnion (fun j => (hj j).preimage
    (((measurable_lMinusSidePresentation_code x).fst.comp measurable_fst).comp
      measurable_subtype_coe))

/-- Helper toward Lemma 5.5. Canonical retained-face succession is exactly
the countable union of the two raw block relations with their canonical IDs. -/
theorem lMinusCanonicalSideOnCoherent_faceNext_iff (x : XDP)
    (z : LMinusCanonicalCodingDomain x) (d e : ℕ × Bool) :
    (lMinusCanonicalSideOnCoherent x z).faceNext d e ↔
      (∃ a b : ℕ × Bool,
        lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2) (lMinusCodePrimedDart z.val.1 (lMinusCoherentLeftSide x z.val.2) a) = d ∧
        lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2) (lMinusCodePrimedDart z.val.1 (lMinusCoherentLeftSide x z.val.2) b) = e ∧
        (∃ j : TriangleCreationTime z.val.1.code.1,
          a ∈ stageTriangleDartList z.val.1.code.1 j) ∧
        kmswInfFaceSucc z.val.1.code.1 z.property a = b) ∨
      ∃ a b : ℕ × Bool,
        a.1 ∈ (lMinusCoherentLeftSide x z.val.2).edges ∧
        b.1 ∈ (lMinusCoherentLeftSide x z.val.2).edges ∧
        (lMinusCoherentEdgeId z.val (.inr a.1), a.2) = d ∧
        (lMinusCoherentEdgeId z.val (.inr b.1), b.2) = e ∧
        (lMinusCoherentLeftSide x z.val.2).faceNext a b := by
  constructor
  · rintro ⟨u, v, hu, hv, h⟩
    rcases h with ⟨a, b, ha, hb, j, hj, hs⟩ | ⟨a, b, ha, hb, hs⟩
    · subst u
      subst v
      exact Or.inl ⟨a, b, hu, hv, ⟨j, hj⟩, hs⟩
    · subst u
      subst v
      exact Or.inr ⟨a.val, b.val, a.property, b.property,
        (lMinusCanonicalHattedRawDartId_eq x z a).trans hu,
        (lMinusCanonicalHattedRawDartId_eq x z b).trans hv, hs⟩
  · rintro (⟨a, b, ha, hb, ⟨j, hj⟩, hs⟩ | ⟨a, b, ham, hbm, ha, hb, hs⟩)
    · exact ⟨_, _, ha, hb, Or.inl ⟨a, b, rfl, rfl, j, hj, hs⟩⟩
    · exact ⟨_, _, (lMinusCanonicalHattedRawDartId_eq x z ⟨a, ham⟩).symm.trans ha,
        (lMinusCanonicalHattedRawDartId_eq x z ⟨b, hbm⟩).symm.trans hb,
        Or.inr ⟨⟨a, ham⟩, ⟨b, hbm⟩, rfl, rfl, hs⟩⟩

/-- Helper toward Lemma 5.5. Every canonical retained-face coordinate is
measurable on certified coherent pairs, preserving both block face families. -/
theorem measurableSet_lMinusCanonicalSideOnCoherent_faceNext
    (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      (lMinusCanonicalSideOnCoherent x z).faceNext d e} := by
  simp only [lMinusCanonicalSideOnCoherent_faceNext_iff, Set.ofPred_or,
    Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
      ((measurable_lMinusCanonicalPrimedDartId x a).eq_const d).setOf.inter
      (((measurable_lMinusCanonicalPrimedDartId x b).eq_const e).setOf.inter
      ((measurableSet_lMinusPrimedTriangleDart x a).inter
        ((measurable_lMinusCanonicalCodingDomain_primedFaceSucc x a).eq_const b).setOf))))
  · exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
      ((measurableSet_lMinusCoherentLeftSide_edges x a.1).preimage
        (measurable_snd.comp measurable_subtype_coe)).inter
      (((measurableSet_lMinusCoherentLeftSide_edges x b.1).preimage
        (measurable_snd.comp measurable_subtype_coe)).inter
      (((measurable_lMinusCanonicalHattedRawDartId x a).eq_const d).setOf.inter
      (((measurable_lMinusCanonicalHattedRawDartId x b).eq_const e).setOf.inter
      ((measurableSet_lMinusCoherentLeftSide_faceNext x a b).preimage
        (measurable_snd.comp measurable_subtype_coe)))))))

/-- Helper toward Lemma 5.5. The graph of a permutation in injective
countable coordinates, without choosing an inverse outside its carrier. -/
@[expose] def lMinusEncodedPermGraph {α β : Type*} (f : α → β)
    (p : Equiv.Perm α) (d e : β) : Prop :=
  ∃ a, f a = d ∧ f (p a) = e

/-- Helper toward Lemma 5.5. Products of encoded permutation graphs are
relational compositions; injectivity preserves the intermediate cell. -/
theorem lMinusEncodedPermGraph_mul {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (p q : Equiv.Perm α) (d e : β) :
    lMinusEncodedPermGraph f (p * q) d e ↔
      ∃ m, lMinusEncodedPermGraph f q d m ∧ lMinusEncodedPermGraph f p m e := by
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨f (q a), ⟨a, ha, rfl⟩, ⟨q a, rfl, hb⟩⟩
  · rintro ⟨m, ⟨a, ha, hm⟩, ⟨b, hb, he⟩⟩
    have hab := hf (hm.trans hb.symm)
    subst b
    exact ⟨a, ha, he⟩

/-- Helper toward Lemma 5.5. Extending a block permutation adds precisely
the fixed darts outside the embedded block, within the geometric carrier. -/
theorem lMinusEncodedPermGraph_extend {α β γ : Type*} (f : β → γ)
    (hf : Function.Injective f) (j : α → β) (hj : Function.Injective j)
    (p : Equiv.Perm α) (d e : γ) :
    lMinusEncodedPermGraph f (p.extendDomain (Equiv.ofInjective j hj)) d e ↔
      lMinusEncodedPermGraph (f ∘ j) p d e ∨
        (d = e ∧ d ∈ Set.range f ∧
          ¬ ∃ m, lMinusEncodedPermGraph (f ∘ j) p d m) := by
  have happ (a : α) : p.extendDomain (Equiv.ofInjective j hj) (j a) = j (p a) :=
    Equiv.Perm.extendDomain_apply_image p (Equiv.ofInjective j hj) a
  constructor
  · rintro ⟨b, hb, he⟩
    by_cases h : b ∈ Set.range j
    · obtain ⟨a, rfl⟩ := h
      exact Or.inl ⟨a, hb, by change f (j (p a)) = e; rw [← happ]; exact he⟩
    · have hfix := Equiv.Perm.extendDomain_apply_not_subtype p
        (Equiv.ofInjective j hj) h
      refine Or.inr ⟨hb.symm.trans (hfix ▸ he), ⟨b, hb⟩, ?_⟩
      rintro ⟨m, a, ha, _⟩
      exact h ⟨a, hf (ha.trans hb.symm)⟩
  · rintro (⟨a, ha, he⟩ | ⟨hde, ⟨b, hb⟩, hn⟩)
    · exact ⟨j a, ha, by rw [happ]; exact he⟩
    · have h : b ∉ Set.range j := by
        rintro ⟨a, rfl⟩
        exact hn ⟨f (j (p a)), a, hb, rfl⟩
      exact ⟨b, hb, (congrArg f (Equiv.Perm.extendDomain_apply_not_subtype p
        (Equiv.ofInjective j hj) h)).trans (hb.trans hde)⟩

/-- Helper toward Lemma 5.5. The hatted block permutation graph has
measurable canonical coordinates on certified coherent pairs. -/
theorem measurableSet_lMinusCanonicalHattedRotationGraph (x : XDP)
    (d e : ℕ × Bool) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      lMinusEncodedPermGraph
        (lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2) ∘
          lMinusCodeHattedDart z.val.1 (lMinusCoherentLeftSide x z.val.2))
        (lMinusHattedRotation x z.val.2) d e} := by
  have he : {z : LMinusCanonicalCodingDomain x |
      lMinusEncodedPermGraph
        (lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2) ∘
          lMinusCodeHattedDart z.val.1 (lMinusCoherentLeftSide x z.val.2))
        (lMinusHattedRotation x z.val.2) d e} =
      {z | ∃ a b : ℕ × Bool,
        a.1 ∈ (lMinusCoherentLeftSide x z.val.2).edges ∧
        b.1 ∈ (lMinusCoherentLeftSide x z.val.2).edges ∧
        (lMinusCoherentEdgeId z.val (.inr a.1), a.2) = d ∧
        (lMinusCoherentEdgeId z.val (.inr b.1), b.2) = e ∧
        (lMinusCoherentLeftSide x z.val.2).rotation a b} := by
    ext z
    constructor
    · rintro ⟨a, ha, hb⟩
      let b := lMinusHattedRotation x z.val.2 a
      exact ⟨a.val, b.val, a.property, b.property,
        (lMinusCanonicalHattedRawDartId_eq x z a).trans ha,
        (lMinusCanonicalHattedRawDartId_eq x z b).trans hb,
        (lMinusHattedRotation_iff x z.val.2 a b).mpr rfl⟩
    · rintro ⟨a, b, ham, hbm, ha, hb, hr⟩
      have h := (lMinusHattedRotation_iff x z.val.2 ⟨a, ham⟩ ⟨b, hbm⟩).mp hr
      refine ⟨⟨a, ham⟩, (lMinusCanonicalHattedRawDartId_eq x z ⟨a, ham⟩).symm.trans ha, ?_⟩
      rw [h]
      exact (lMinusCanonicalHattedRawDartId_eq x z ⟨b, hbm⟩).symm.trans hb
  rw [he]
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    ((measurableSet_lMinusCoherentLeftSide_edges x a.1).preimage
      (measurable_snd.comp measurable_subtype_coe)).inter
    (((measurableSet_lMinusCoherentLeftSide_edges x b.1).preimage
      (measurable_snd.comp measurable_subtype_coe)).inter
    (((measurable_lMinusCanonicalHattedRawDartId x a).eq_const d).setOf.inter
    (((measurable_lMinusCanonicalHattedRawDartId x b).eq_const e).setOf.inter
    ((measurableSet_lMinusCoherentLeftSide_rotation x a b).preimage
      (measurable_snd.comp measurable_subtype_coe)))))))

/-- Helper toward Lemma 5.5. The primed block permutation graph has
measurable canonical coordinates, with the original orientation correction. -/
theorem measurableSet_lMinusCanonicalPrimedRotationGraph (x : XDP)
    (d e : ℕ × Bool) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      lMinusEncodedPermGraph
        (lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2) ∘
          lMinusCodePrimedDart z.val.1 (lMinusCoherentLeftSide x z.val.2))
        (kmswInfRot z.val.1.code.1 z.property) d e} := by
  have he : {z : LMinusCanonicalCodingDomain x |
      lMinusEncodedPermGraph
        (lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2) ∘
          lMinusCodePrimedDart z.val.1 (lMinusCoherentLeftSide x z.val.2))
        (kmswInfRot z.val.1.code.1 z.property) d e} =
      {z | ∃ a b : ℕ × Bool,
        lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2)
          (lMinusCodePrimedDart z.val.1 _ a) = d ∧
        lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2)
          (lMinusCodePrimedDart z.val.1 _ b) = e ∧
        kmswInfRot z.val.1.code.1 z.property a = b} := by
    ext z
    exact ⟨fun ⟨a, ha, hb⟩ => ⟨a, _, ha, hb, rfl⟩,
      fun ⟨a, b, ha, hb, hr⟩ => ⟨a, ha, hr ▸ hb⟩⟩
  rw [he]
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    ((measurable_lMinusCanonicalPrimedDartId x a).eq_const d).setOf.inter
    (((measurable_lMinusCanonicalPrimedDartId x b).eq_const e).setOf.inter
    ((measurable_lMinusCanonicalCodingDomain_primedRotation x a).eq_const b).setOf)))

/-- Helper toward Lemma 5.5. Left boundary edge labels are measurable
through the countable record selector, including its original totalization. -/
theorem measurable_lMinusLeftBoundaryEdge_code (i : ℕ) :
    Measurable (fun c : ℕ → Fin 3 =>
      kmswLeftBoundaryEdge (boltzmannKMSWStream c) i) := by
  let P : (ℕ → Fin 3) → ℕ → Prop := fun c m =>
    ∀ j, m < j → L (boltzmannKMSWStream c) m + 1 ≤ L (boltzmannKMSWStream c) j
  have hL (n : ℕ) : Measurable (fun c : ℕ → Fin 3 =>
      L (boltzmannKMSWStream c) n) := by
    refine measurable_of_factors_prefix (n + 1) _ ?_
    intro c c' hc
    apply L_congr
    intro j hj
    simpa only [boltzmannKMSWStream] using hc (j + 1) (by omega)
  have hP (m : ℕ) : MeasurableSet {c : ℕ → Fin 3 | P c m} := by
    have he : {c : ℕ → Fin 3 | P c m} = ⋂ j : ℕ, ⋂ (_ : m < j),
        {c | L (boltzmannKMSWStream c) m + 1 ≤ L (boltzmannKMSWStream c) j} := by
      ext c
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, P]
    rw [he]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
      measurableSet_le ((hL m).add_const 1) (hL j)))
  have hcount (n : ℕ) : Measurable (fun c : ℕ → Fin 3 => Nat.count (P c) n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      simp only [Nat.count_succ]
      exact ih.add (measurable_const.ite (hP n) measurable_const)
  have ht (m : ℕ) : MeasurableSet {c : ℕ → Fin 3 |
      i < Nat.count (P c) (m + 1)} :=
    (hcount (m + 1)) (Set.to_countable {n : ℕ | i < n}).measurableSet
  have hE : MeasurableSet {c : ℕ → Fin 3 | ∃ m, i < Nat.count (P c) (m + 1)} := by
    simpa only [Set.iUnion_ofPred] using MeasurableSet.iUnion ht
  have hfind : Measurable (fun c : {c : ℕ → Fin 3 |
      ∃ m, i < Nat.count (P c) (m + 1)} => Nat.find c.2) :=
    measurable_find (fun c => c.2) (fun m => (ht m).preimage measurable_subtype_coe)
  have hselect : Measurable (fun c : ℕ → Fin 3 => natSelect (P c) i) := by
    convert hfind.dite measurable_const hE using 1
    funext c
    simp only [natSelect, P]
    congr 2
  have hact (m : ℕ) : Measurable (fun c : ℕ → Fin 3 =>
      act (boltzmannKMSWStream c) m) := by
    refine measurable_of_factors_prefix (m + 1) _ ?_
    intro c c' hc
    unfold act boltzmannKMSWStream
    rw [kmswStage_congr (fun j hj => hc (j + 1) (by omega))]
  have hpair : Measurable (fun z : ℕ × (ℕ → Fin 3) =>
      act (boltzmannKMSWStream z.2) z.1) :=
    measurable_from_prod_countable_right hact
  simpa only [kmswLeftBoundaryEdge, P, Function.comp_def, id_eq] using
    hpair.comp (hselect.prodMk measurable_id)

/-- Helper toward Lemma 5.5. Every interface dart has a measurable
canonical ID, retaining its boundary index and its endpoint bit. -/
theorem measurable_lMinusCanonicalBoundaryDartId (x : XDP) (d : ℕ × Bool) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2)
        (lMinusCodeBoundaryDart z.val.1 z.val.2 d)) := by
  have hs : Measurable (fun q : Coherent x =>
      (lMinusCoherentLeftSide x q).boundary d.1) :=
    ((measurable_lMinusLeftBoundaryEdge_code d.1).comp
      (measurable_pathCode.comp measurable_subtype_coe)).prodMk measurable_const
  have hraw : Measurable (fun z : LMinusCanonicalCodingDomain x =>
      (Sum.inr ((lMinusCoherentLeftSide x z.val.2).boundary d.1).1 : Sum ℕ ℕ)) :=
    measurable_inr.comp ((hs.fst).comp
      (measurable_snd.comp measurable_subtype_coe))
  have hid := (measurable_lMinusCoherentEdgeId_uncurry x).comp
    (hraw.prodMk measurable_subtype_coe)
  convert hid.prodMk (measurable_const (a := d.2)) using 1
  funext z
  exact Prod.ext (lMinusCoherentEdgeId_eq z.val.1 z.val.2
    (.inr ⟨((lMinusCoherentLeftSide x z.val.2).boundary d.1).1,
      lMinus_hatted_boundary_mem x z.val.2 d.1⟩)).symm rfl

/-- Helper toward Lemma 5.5. The interface correction graph is measurable
in the same canonical dart coordinates as the two block graphs. -/
theorem measurableSet_lMinusCanonicalCornerGraph (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      lMinusEncodedPermGraph
        (lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2) ∘
          lMinusCodeBoundaryDart z.val.1 z.val.2) lMinusBoundaryCornerPerm d e} := by
  change MeasurableSet {z : LMinusCanonicalCodingDomain x | ∃ a : ℕ × Bool,
    lMinusCanonicalDartId z.val.1 _ (lMinusCodeBoundaryDart z.val.1 z.val.2 a) = d ∧
    lMinusCanonicalDartId z.val.1 _ (lMinusCodeBoundaryDart z.val.1 z.val.2
      (lMinusBoundaryCornerPerm a)) = e}
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a =>
    ((measurable_lMinusCanonicalBoundaryDartId x a).eq_const d).setOf.inter
      ((measurable_lMinusCanonicalBoundaryDartId x (lMinusBoundaryCornerPerm a)).eq_const e).setOf)

/-- Helper toward Lemma 5.5. A swap has its literal two moved-coordinate
branches and fixes every other allocated coordinate. -/
theorem lMinusEncodedPermGraph_swap {α β : Type*} [DecidableEq α] (f : α → β)
    (hf : Function.Injective f) (a b : α) (d e : β) :
    lMinusEncodedPermGraph f (Equiv.swap a b) d e ↔
      (d = f a ∧ e = f b) ∨ (d = f b ∧ e = f a) ∨
        (d ≠ f a ∧ d ≠ f b ∧ d = e ∧ d ∈ Set.range f) := by
  constructor
  · rintro ⟨u, hu, hv⟩
    by_cases ha : u = a
    · subst u
      exact Or.inl ⟨hu.symm, by simpa only [Equiv.swap_apply_left] using hv.symm⟩
    · by_cases hb : u = b
      · subst u
        exact Or.inr (Or.inl ⟨hu.symm, by simpa only [Equiv.swap_apply_right] using hv.symm⟩)
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb] at hv
        exact Or.inr (Or.inr ⟨fun h => ha (hf (hu.trans h)),
          fun h => hb (hf (hu.trans h)), hu.symm.trans hv, u, hu⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, hb, rfl, u, hu⟩)
    · exact ⟨a, rfl, congrArg f (Equiv.swap_apply_left a b)⟩
    · exact ⟨b, rfl, congrArg f (Equiv.swap_apply_right a b)⟩
    · refine ⟨u, hu, ?_⟩
      rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha (hu.symm.trans (congrArg f h)))
        (fun h => hb (hu.symm.trans (congrArg f h)))]
      exact hu

/-- Helper toward Lemma 5.5. Every canonical rotation coordinate is
measurable on certified coherent pairs, including the initial adjustment. -/
theorem measurableSet_lMinusCanonicalSideOnCoherent_rotation
    (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      (lMinusCanonicalSideOnCoherent x z).rotation d e} := by
  let Z := LMinusCanonicalCodingDomain x
  let A (z : Z) := LMinusCodeGluedDart z.val.1 (lMinusCoherentLeftSide x z.val.2)
  let F (z : Z) : A z → ℕ × Bool :=
    lMinusCanonicalDartId z.val.1 (lMinusCoherentLeftSide x z.val.2)
  have hF (z : Z) : Function.Injective (F z) := lMinusCanonicalDartId_injective _ _
  let G (P : (z : Z) → Equiv.Perm (A z)) (a b : ℕ × Bool) : Set Z :=
    {z | lMinusEncodedPermGraph (F z) (P z) a b}
  have hAlloc (a : ℕ × Bool) : MeasurableSet {z : Z | a ∈ Set.range (F z)} := by
    have he : {z : Z | a ∈ Set.range (F z)} =
        {z : Z | a.1 ∈ (lMinusCanonicalSideOnCoherent x z).edges} := by
      ext z
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨u.1, congrArg Prod.fst hu⟩
      · rintro ⟨u, hu⟩
        exact ⟨(u, a.2), Prod.ext hu rfl⟩
    rw [he]
    exact measurableSet_lMinusCanonicalSideOnCoherent_edges x a.1
  have hMul (P Q : (z : Z) → Equiv.Perm (A z))
      (hP : ∀ a b, MeasurableSet (G P a b))
      (hQ : ∀ a b, MeasurableSet (G Q a b)) (a b : ℕ × Bool) :
      MeasurableSet (G (fun z => P z * Q z) a b) := by
    have he : G (fun z => P z * Q z) a b = ⋃ m, G Q a m ∩ G P m b := by
      ext z
      simpa only [G, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff] using
        lMinusEncodedPermGraph_mul (F z) (hF z) (P z) (Q z) a b
    rw [he]
    exact MeasurableSet.iUnion (fun m => (hQ a m).inter (hP m b))
  have hExt (T : Z → Type) (j : (z : Z) → T z → A z)
      (hj : ∀ z, Function.Injective (j z)) (P : (z : Z) → Equiv.Perm (T z))
      (hP : ∀ a b, MeasurableSet {z : Z |
        lMinusEncodedPermGraph (F z ∘ j z) (P z) a b}) (a b : ℕ × Bool) :
      MeasurableSet (G (fun z => (P z).extendDomain (Equiv.ofInjective (j z) (hj z))) a b) := by
    have he : G (fun z => (P z).extendDomain (Equiv.ofInjective (j z) (hj z))) a b =
        {z | lMinusEncodedPermGraph (F z ∘ j z) (P z) a b} ∪
        ({z : Z | a = b} ∩ {z : Z | a ∈ Set.range (F z)} ∩
          (⋃ m, {z : Z | lMinusEncodedPermGraph (F z ∘ j z) (P z) a m})ᶜ) := by
      ext z
      simpa only [G, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_iUnion, and_assoc] using
        lMinusEncodedPermGraph_extend (F z) (hF z) (j z) (hj z) (P z) a b
    rw [he]
    exact (hP a b).union (((MeasurableSet.const (a = b)).inter (hAlloc a)).inter
      (MeasurableSet.iUnion (fun m => hP a m)).compl)
  have hEval (P : (z : Z) → Equiv.Perm (A z))
      (hP : ∀ a b, MeasurableSet (G P a b)) (u v : Z → ℕ × Bool)
      (hu : Measurable u) (hv : Measurable v) :
      MeasurableSet {z | lMinusEncodedPermGraph (F z) (P z) (u z) (v z)} := by
    have he : {z | lMinusEncodedPermGraph (F z) (P z) (u z) (v z)} =
        ⋃ a : ℕ × Bool, ⋃ b : ℕ × Bool,
          {z | u z = a} ∩ {z | v z = b} ∩ G P a b := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, G]
      exact ⟨fun h => ⟨u z, v z, ⟨rfl, rfl⟩, h⟩,
        fun ⟨a, b, ⟨ha, hb⟩, h⟩ => ha.symm ▸ hb.symm ▸ h⟩
    rw [he]
    exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
      (((hu.eq_const a).setOf).inter (hv.eq_const b).setOf).inter (hP a b)))
  have hApply (P : (z : Z) → Equiv.Perm (A z))
      (hP : ∀ a b, MeasurableSet (G P a b)) (u : (z : Z) → A z)
      (hu : Measurable (fun z => F z (u z))) :
      Measurable (fun z => F z (P z (u z))) := by
    apply measurable_to_countable'
    intro b
    have he : {z : Z | F z (P z (u z)) = b} =
        {z | lMinusEncodedPermGraph (F z) (P z) (F z (u z)) b} := by
      ext z
      constructor
      · intro h
        exact ⟨u z, rfl, h⟩
      · rintro ⟨v, hv, he⟩
        have hvu := hF z hv
        rw [hvu] at he
        exact he
    change MeasurableSet {z : Z | F z (P z (u z)) = b}
    rw [he]
    exact hEval P hP _ _ hu measurable_const
  have hSwap (u v : (z : Z) → A z)
      (hu : Measurable (fun z => F z (u z)))
      (hv : Measurable (fun z => F z (v z))) (a b : ℕ × Bool) :
      MeasurableSet (G (fun z => Equiv.swap (u z) (v z)) a b) := by
    have he : G (fun z => Equiv.swap (u z) (v z)) a b =
        {z | (a = F z (u z) ∧ b = F z (v z)) ∨
          (a = F z (v z) ∧ b = F z (u z)) ∨
          (a ≠ F z (u z) ∧ a ≠ F z (v z) ∧ a = b ∧ a ∈ Set.range (F z))} := by
      ext z
      exact lMinusEncodedPermGraph_swap (F z) (hF z) (u z) (v z) a b
    rw [he]
    simp only [Set.ofPred_or, Set.ofPred_and]
    exact (((measurable_const.eq hu).setOf).inter (measurable_const.eq hv).setOf).union
      ((((measurable_const.eq hv).setOf).inter (measurable_const.eq hu).setOf).union
      (((measurable_const.eq hu).setOf.compl).inter
      (((measurable_const.eq hv).setOf.compl).inter
      ((MeasurableSet.const (a = b)).inter (hAlloc a)))))
  let H (z : Z) := (lMinusHattedRotation x z.val.2).extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective z.val.1 z.val.2))
  have hH : ∀ a b, MeasurableSet (G H a b) :=
    hExt _ _ (fun z => lMinusCodeHattedDart_injective z.val.1 z.val.2) _
      (measurableSet_lMinusCanonicalHattedRotationGraph x)
  have hPr : ∀ a b, MeasurableSet (G (fun z =>
      (kmswInfRot z.val.1.code.1 z.property).extendDomain
        (Equiv.ofInjective _ (lMinusCodePrimedDart_injective z.val.1 z.val.2))) a b) :=
    hExt _ _ (fun z => lMinusCodePrimedDart_injective z.val.1 z.val.2) _
      (measurableSet_lMinusCanonicalPrimedRotationGraph x)
  have hC : ∀ a b, MeasurableSet (G (fun z => lMinusBoundaryCornerPerm.extendDomain
      (Equiv.ofInjective _ (lMinusCodeBoundaryDart_injective z.val.1 z.val.2))) a b) :=
    hExt _ _ (fun z => lMinusCodeBoundaryDart_injective z.val.1 z.val.2) _
      (measurableSet_lMinusCanonicalCornerGraph x)
  have hSp : ∀ a b, MeasurableSet (G (fun z =>
      lMinusCodeSpliceRotation z.val.1 z.val.2 z.property) a b) :=
    hMul _ _ (hMul _ _ hPr hC) hH
  let c (z : Z) : A z := lMinusCodeBoundaryDart z.val.1 z.val.2 (0, false)
  let a (z : Z) : A z := (H z).symm (c z)
  have hc : Measurable (fun z => F z (c z)) := measurable_lMinusCanonicalBoundaryDartId x _
  have hHi : ∀ u v, MeasurableSet (G (fun z => (H z).symm) u v) := by
    intro u v
    have he : G (fun z => (H z).symm) u v = G H v u := by
      ext z
      constructor
      · rintro ⟨b, hb, he⟩
        exact ⟨(H z).symm b, he, by simpa only [Equiv.apply_symm_apply] using hb⟩
      · rintro ⟨b, hb, he⟩
        exact ⟨H z b, he, by simpa only [Equiv.symm_apply_apply] using hb⟩
    rw [he]
    exact hH v u
  have ha : Measurable (fun z => F z (a z)) := hApply _ hHi c hc
  let B (z : Z) := lMinusCodeInitialAdjustedRotation z.val.1 z.val.2 z.property
  have hB : ∀ u v, MeasurableSet (G B u v) := hMul _ _ hSp (hSwap c a hc ha)
  have hBa : Measurable (fun z => F z (B z (a z))) := hApply B hB a ha
  have hFinal := hMul _ _ (hSwap (fun z => B z (a z)) c hBa hc) hB d e
  have heq : {z : Z | a z = c z} = {z : Z | F z (a z) = F z (c z)} := by
    ext z
    exact (hF z).eq_iff.symm
  have hEq : MeasurableSet {z : Z | a z = c z} := by
    rw [heq]
    exact (ha.eq hc).setOf
  have he : {z : Z | (lMinusCanonicalSideOnCoherent x z).rotation d e} =
      ({z : Z | a z = c z} ∩ G B d e) ∪
        ({z : Z | a z ≠ c z} ∩ G (fun z => Equiv.swap (B z (a z)) (c z) * B z) d e) := by
    ext z
    change (∃ u v, F z u = d ∧ F z v = e ∧
      (if a z = c z then B z else Equiv.swap (B z (a z)) (c z) * B z) u = v) ↔
      (a z = c z ∧ lMinusEncodedPermGraph (F z) (B z) d e) ∨
      (a z ≠ c z ∧ lMinusEncodedPermGraph (F z)
        (Equiv.swap (B z (a z)) (c z) * B z) d e)
    by_cases h : a z = c z
    · rw [ite_eq_left h]
      constructor
      · rintro ⟨u, v, hu, hv, he⟩
        exact Or.inl ⟨h, u, hu, he ▸ hv⟩
      · rintro (⟨_, u, hu, hv⟩ | ⟨hn, _⟩)
        · exact ⟨u, _, hu, hv, rfl⟩
        · exact False.elim (hn h)
    · rw [ite_eq_right h]
      constructor
      · rintro ⟨u, v, hu, hv, he⟩
        exact Or.inr ⟨h, u, hu, he ▸ hv⟩
      · rintro (⟨hn, _⟩ | ⟨_, u, hu, hv⟩)
        · exact False.elim (h hn)
        · exact ⟨u, _, hu, hv, rfl⟩
  rw [he]
  exact (hEq.inter (hB d e)).union (hEq.compl.inter hFinal)

/-- Helper toward Lemma 5.5. All ten canonical geometric-side fields
are jointly measurable on the certified coherent-pair domain. -/
theorem measurable_lMinusCanonicalSideOnCoherent_code (x : XDP) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      geometricSideCode (lMinusCanonicalSideOnCoherent x z)) := by
  have hBool (P : LMinusCanonicalCodingDomain x → Prop)
      (hP : MeasurableSet {z | P z}) : Measurable (fun z => decide (P z)) := by
    apply measurable_to_bool
    change MeasurableSet {z : LMinusCanonicalCodingDomain x | decide (P z) = true}
    simpa only [decide_eq_true_eq] using hP
  have hv (n : ℕ) := hBool _ (measurableSet_lMinusCanonicalSideOnCoherent_vertices x n)
  have he (n : ℕ) := hBool _ (measurableSet_lMinusCanonicalSideOnCoherent_edges x n)
  have hp (n : ℕ) := hBool _ (measurableSet_lMinusCanonicalSideOnCoherent_present x n)
  have hr (d e : ℕ × Bool) :=
    hBool _ (measurableSet_lMinusCanonicalSideOnCoherent_rotation x d e)
  have hf (d e : ℕ × Bool) :=
    hBool _ (measurableSet_lMinusCanonicalSideOnCoherent_faceNext x d e)
  exact (measurable_pi_iff.mpr hv).prodMk
    ((measurable_pi_iff.mpr he).prodMk
    ((measurable_pi_iff.mpr (measurable_lMinusCanonicalSideOnCoherent_endpoint x false)).prodMk
    ((measurable_pi_iff.mpr (measurable_lMinusCanonicalSideOnCoherent_endpoint x true)).prodMk
    ((measurable_pi_iff.mpr hp).prodMk
    ((measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr (hr d))).prodMk
    ((measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr (hf d))).prodMk
    ((measurable_lMinusCanonicalSideOnCoherent_root x).prodMk
    ((measurable_pi_iff.mpr (measurable_lMinusCanonicalSideOnCoherent_boundary x)).prodMk
      (measurable_pi_iff.mpr (measurable_lMinusCanonicalSideOnCoherent_seam x))))))))))

/-- Helper toward Lemma 5.5. The canonical side itself is measurable
for the sigma algebra generated by all ten geometric-side fields. -/
theorem measurable_lMinusCanonicalSideOnCoherent (x : XDP) :
    Measurable (lMinusCanonicalSideOnCoherent x) :=
  measurable_comap_iff.mpr (measurable_lMinusCanonicalSideOnCoherent_code x)

/-- Helper toward Lemma 5.5. Passing to marked-isomorphism classes
preserves the proved coherent-pair measurability. -/
theorem measurable_lMinusCanonicalSideOnCoherent_class (x : XDP) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      geometricSideClass (lMinusCanonicalSideOnCoherent x z)) :=
  measurable_geometricSideClass.comp (measurable_lMinusCanonicalSideOnCoherent x)

/-- Helper toward Lemma 5.5. Equal hatted truncation codes identify the
canonical classes for a fixed primed presentation; ambient raw IDs need not agree. -/
theorem lMinusCanonicalSide_class_eq_of_thinSideCode_eq (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q.val =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q'.val) :
    geometricSideClass (lMinusCanonicalSide x r q hf) =
      geometricSideClass (lMinusCanonicalSide x r q' hf) := by
  rw [lMinusCanonicalSide_class_eq, lMinusCanonicalSide_class_eq]
  exact (geometricSideClass_eq_iff _ _).mpr
    (lMinusCodeSide4_markedIso x r q q'
      (leftSideCode_markedIso_of_eq x q q' hc).some hf)

/-- Helper toward Lemma 5.5. The optional canonical class on raw pairs
is present exactly when its primed incidence and hatted coherence certificates
hold. This domain is larger than source-valid presentation preimages. -/
@[expose] noncomputable def lMinusRawCanonicalClassOption (x : XDP)
    (z : LMinusSidePresentation x × (ℕ → ℤ × ℤ)) : Option GeometricSideClass :=
  if h : KMSWFiniteIncidence z.1.code.1 ∧ z.2 ∈ Coherent x then
    some (geometricSideClass (lMinusCanonicalSide x z.1 ⟨z.2, h.2⟩ h.1))
  else none

/-- Helper toward Lemma 5.5. The optional canonical class is measurable
on raw presentation/path pairs, with its exact certification domain. -/
theorem measurable_lMinusRawCanonicalClassOption (x : XDP) :
    Measurable (lMinusRawCanonicalClassOption x) := by
  let D : Set (LMinusSidePresentation x × (ℕ → ℤ × ℤ)) :=
    {z | KMSWFiniteIncidence z.1.code.1 ∧ z.2 ∈ Coherent x}
  have hD : MeasurableSet D :=
    (measurableSet_finiteIncidence.preimage
      ((measurable_lMinusSidePresentation_code x).fst.comp measurable_fst)).inter
    ((selectedCutCoherentDomain_measurable_conull x renewalTime
      renewalTime_positiveSuccessTime).1.preimage measurable_snd)
  let f (z : D) : LMinusCanonicalCodingDomain x :=
    ⟨(z.val.1, ⟨z.val.2, z.property.2⟩), z.property.1⟩
  have hm : Measurable f :=
    ((measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)).subtype_mk
  have hclass : Measurable (fun z : D =>
      some (geometricSideClass (lMinusCanonicalSideOnCoherent x (f z)))) :=
    (measurable_some_geometricSideClass.comp
      (measurable_lMinusCanonicalSideOnCoherent_class x)).comp hm
  exact hclass.dite measurable_const hD

/-- Helper toward Lemma 5.5. The exact optional class reader composed
with the source observation is a.e. measurable. This does not assert descent
to the observation law. -/
theorem aemeasurable_decodeLMinus_leftSideObsNonpos_classOption4
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable (fun W =>
      (decodeLMinus x k (leftSideObsNonpos x k W)).classOption4)
      wholePlaneIIDCodeMeasure := by
  have hm := (measurable_lMinusRawCanonicalClassOption x).comp_aemeasurable
    ((aemeasurable_decodeLMinus_leftSideObsNonpos x k).prodMk
      (aemeasurable_boundaryFutureHattedPath k))
  apply hm.congr
  filter_upwards [ae_boundaryGluing_nonpos_left_class_eq_lMinusDecodedSide4] with W hW
  change lMinusRawCanonicalClassOption x
    (decodeLMinus x k (leftSideObsNonpos x k W), boundaryFutureHattedPath k W) =
      (decodeLMinus x k (leftSideObsNonpos x k W)).classOption4
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hW
  cases x with
  | ldp =>
    obtain ⟨R, T, P, _, _, _, _, hclass⟩ := hpaths true
    obtain ⟨hτ, hfin, hq, he, hr⟩ := hclass k hk
    have hf := lMinus_primed_observation_finiteIncidence (longest := true) hτ hfin
    change KMSWFiniteIncidence (decodeLMinus XDP.ldp k
      (leftSideObsNonpos XDP.ldp k W)).code.1 at hf
    change boundaryFutureHattedPath k W ∈ Coherent XDP.ldp at hq
    dsimp only [lMinusRawCanonicalClassOption, Prod.fst, Prod.snd]
    rw [dite_eq_left ⟨hf, hq⟩]
    exact (congrArg some (lMinusCanonicalSide_class_eq_decodedSide4
      (longest := true) hτ hq hfin)).trans
      ((congrArg some he).symm.trans hr.symm)
  | sdp =>
    obtain ⟨R, T, P, _, _, _, _, hclass⟩ := hpaths false
    obtain ⟨hτ, hfin, hq, he, hr⟩ := hclass k hk
    have hf := lMinus_primed_observation_finiteIncidence (longest := false) hτ hfin
    change KMSWFiniteIncidence (decodeLMinus XDP.sdp k
      (leftSideObsNonpos XDP.sdp k W)).code.1 at hf
    change boundaryFutureHattedPath k W ∈ Coherent XDP.sdp at hq
    dsimp only [lMinusRawCanonicalClassOption, Prod.fst, Prod.snd]
    rw [dite_eq_left ⟨hf, hq⟩]
    exact (congrArg some (lMinusCanonicalSide_class_eq_decodedSide4
      (longest := false) hτ hq hfin)).trans
      ((congrArg some he).symm.trans hr.symm)

/-- Helper toward Lemma 5.5. A common measurable conull source domain
makes both the presentation observation and its exact class reader measurable,
and every hatted coordinate there belongs to its countable truncation range. -/
theorem exists_measurable_lMinusSourceDomain (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    ∃ S : Set (ℤ → Fin 3), MeasurableSet S ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∈ S) ∧
      (∀ W ∈ S, ∀ i : ℕ,
        (decodeLMinus x k (leftSideObsNonpos x k W)).code.2 i ∈
          Set.range (halfTruncate .left i)) ∧
      Measurable (fun W : S => decodeLMinus x k (leftSideObsNonpos x k W.val)) ∧
      Measurable (fun W : S =>
        (decodeLMinus x k (leftSideObsNonpos x k W.val)).classOption4) := by
  let obs (W : ℤ → Fin 3) := decodeLMinus x k (leftSideObsNonpos x k W)
  let cls (W : ℤ → Fin 3) := (obs W).classOption4
  have ho : AEMeasurable obs wholePlaneIIDCodeMeasure :=
    aemeasurable_decodeLMinus_leftSideObsNonpos x k
  have hc : AEMeasurable cls wholePlaneIIDCodeMeasure :=
    aemeasurable_decodeLMinus_leftSideObsNonpos_classOption4 x k hk
  have hg : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      obs W = ho.mk obs W ∧ cls W = hc.mk cls W ∧
      ∀ i : ℕ, (obs W).code.2 i ∈ Set.range (halfTruncate .left i) := by
    filter_upwards [ho.ae_eq_mk, hc.ae_eq_mk,
      ae_decodeLMinus_leftSideObsNonpos_hatted_mem_range x k hk] with W h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨S, hfull, hS, hgood⟩ := hg.exists_measurable_mem
  refine ⟨S, hS, hfull, fun W hW => (hgood W hW).2.2, ?_, ?_⟩
  · have he : (fun W : S => obs W.val) = fun W : S => ho.mk obs W.val :=
      funext (fun W => (hgood W.val W.property).1)
    change Measurable (fun W : S => obs W.val)
    rw [he]
    exact ho.measurable_mk.comp measurable_subtype_coe
  · have he : (fun W : S => cls W.val) = fun W : S => hc.mk cls W.val :=
      funext (fun W => (hgood W.val W.property).2.1)
    change Measurable (fun W : S => cls W.val)
    rw [he]
    exact hc.measurable_mk.comp measurable_subtype_coe

end DirectedDistances.PaperProofs.Section5










































































/- Quot.sound alone. Every other theorem uses only propext, Classical.choice,
and Quot.sound. No custom axiom or sorryAx occurred in these transitive
probes. The probes were removed before the final production compile.
with the sole coordinator. The predecessor and all other source files were
left unchanged. -/
