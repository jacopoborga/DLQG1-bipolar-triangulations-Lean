/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516RootAlignment
public import DirectedDistances.KMSW.KMSWStageRootedMirror

/- # West-rooted finite KMSW stage laws for Proposition 5.16

is edgeFlip of the existing east dart; its edge ID and the uniform mark are
unchanged.

DirectedDistances/PaperProofs/Section5 and DirectedDistances/KMSW):

* KMSW/KMSWDiskRootedLaw.lean:225-228,234-236,245-255,280-294: west stage,
  decorated identification, and both uniform laws are proved below.
* KMSW/KMSWMirrorRootedLaw.lean:91-148 and
  KMSW/KMSWStageRootedMirror.lean:43-115: the west-rooted decorated mirror
  identity and west-rooted walk-mirror identity are proved below. Their
  underlying sample spaces and uniform weights are unchanged.
* PaperProofs/Section5/Prop59FiniteReflectionGrade2.lean:42-53 and
  DiskRootedMirrorFacedCompat.lean:169-186: these consume rootedStage_walkMirror;
  the west-rooted counterpart is proved below. The planar sample in both uses
  already has its west root by DiskRootedPlanarObject.lean:199-204.
* Geometric selected-edge uses are unaffected: PaperProofs/Section5/
  DiskRootedPlanarObject.lean:258,301,371, DiskWindowDartTransport.lean:831,
  853, DiskBSBallLaw.lean:230-233, DiskRootedMapObject.lean:68,87,
  FacedDiskWindowCompare.lean:221-224,645-657, DiskWindowFramedIso.lean:110,
  191,201-207, and DiskBSBallRestriction.lean:302,655-661,764-891 use the
  same selected edge for edge/missing-edge or ball transport facts; the planar
  root and ball centre are already explicitly flipped west. In KMSW,
  KMSWDiskRootCenter.lean:85-168, KMSWDiskRootOrderedFrame.lean:160-218,
  KMSWWindowCommonRoot.lean:62-82, KMSWWindowDiskRootFrame.lean:169-210,
  and KMSWDiskRootFrameWindowOrder.lean:35-120 retain both dart orientations
  and identify the west-to-east frame; they do not consume the east-rooted law.

These are helper results only; no paper-completion claim is made. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory

/-- Helper toward Proposition 5.16. Flipping the distinguished dart of a
rooted finite directed-map class is well-defined on isomorphism classes. -/
@[expose] def rootedFiniteDirectedMapClassFlip :
    RootedFiniteDirectedMapClass → RootedFiniteDirectedMapClass :=
  Quotient.map
    (fun x : Σ k : ℕ, DirectedMapWithMissing (Fin k) × Fin k =>
      (⟨x.1, ⟨x.2.1, x.2.1.edgeInv x.2.2⟩⟩ :
        Σ k : ℕ, DirectedMapWithMissing (Fin k) × Fin k))
    (by
      intro x y hxy
      change (∃ I : DirectedMapWithMissingIso x.2.1 y.2.1,
        I.toEquiv x.2.2 = y.2.2) at hxy
      rcases hxy with ⟨I, hroot⟩
      change ∃ J : DirectedMapWithMissingIso x.2.1 y.2.1,
        J.toEquiv (x.2.1.edgeInv x.2.2) = y.2.1.edgeInv y.2.2
      refine ⟨I, ?_⟩
      rw [I.edgeInv_comm, hroot])

/-- Helper toward Proposition 5.16. The quotient dart flip is involutive. -/
theorem rootedFiniteDirectedMapClassFlip_involutive
    (C : RootedFiniteDirectedMapClass) :
    rootedFiniteDirectedMapClassFlip
      (rootedFiniteDirectedMapClassFlip C) = C := by
  classical
  refine Quotient.inductionOn C ?_
  rintro ⟨k, M, d⟩
  apply Quotient.sound
  refine ⟨DirectedMapWithMissingIso.refl M, ?_⟩
  exact M.edgeInv_invol d

/-- Helper toward Proposition 5.16. Flipping a rooted class obtained from a
directed map is the same as rooting that map at its opposite dart. -/
theorem rootedFiniteDirectedMapClassFlip_toRootedClass {D : Type*}
    [Fintype D] [DecidableEq D] (M : DirectedMapWithMissing D) (d : D) :
    rootedFiniteDirectedMapClassFlip (M.toRootedClass d) =
      M.toRootedClass (M.edgeInv d) := by
  classical
  let e := Fintype.equivFin D
  have hroot : (M.transport e).edgeInv (e d) = e (M.edgeInv d) :=
    (M.transportIso e).edgeInv_comm d |>.symm
  change rootedFiniteDirectedMapClassFlip
    (Quotient.mk rootedFiniteDirectedMapSetoid
      ⟨Fintype.card D, M.transport e, e d⟩) =
    Quotient.mk rootedFiniteDirectedMapSetoid
      ⟨Fintype.card D, M.transport e, e (M.edgeInv d)⟩
  simp only [rootedFiniteDirectedMapClassFlip, Quotient.map_mk]
  apply Quotient.sound
  exact ⟨DirectedMapWithMissingIso.refl (M.transport e), hroot⟩

/-- Helper toward Proposition 5.16. The west-rooted stage uses the same KMSW
stage and the opposite dart of its sampled missing edge. -/
@[expose] noncomputable def rootedStageWest {ℓ n : ℕ}
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) : RootedFiniteDirectedMapClass :=
  let M := kmswStageDirectedMap (finiteCodeExtend (n := n + 1) p.1.val) n
  M.toRootedClass (edgeFlip _ (kmswDiskRootDart p.1 p.2))

/-- Helper toward Proposition 5.16. The west and east root marks have the same
geometric edge ID. -/
theorem rootedStageWest_edge_eq_rootedStage_edge {ℓ n : ℕ}
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) :
    (edgeFlip _ (kmswDiskRootDart p.1 p.2)).1 =
      (kmswDiskRootDart p.1 p.2).1 := rfl

/-- Helper toward Proposition 5.16. The west-rooted stage class is the flip of
the east-rooted stage class. -/
theorem rootedStageWest_eq_flip_rootedStage {ℓ n : ℕ}
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) :
    rootedStageWest p =
      rootedFiniteDirectedMapClassFlip (rootedStage p) := by
  unfold rootedStageWest rootedStage
  rw [rootedFiniteDirectedMapClassFlip_toRootedClass]
  rfl

/-- Helper toward Proposition 5.16. The west-rooted uniform stage law is the
push-forward of the east-rooted uniform stage law under dart flip. The product
measure on walk classes and marks is unchanged, so each sampled mark retains
its original uniform weight. -/
theorem rootedStageWest_uniform_eq_flip (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
        (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedStageWest =
    (((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedStage).map
        rootedFiniteDirectedMapClassFlip := by
  letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
      (kmswLeftEndpointSideEquiv ℓ n hℓ)
  letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  have hfun : rootedStageWest (ℓ := ℓ) (n := n) =
      rootedFiniteDirectedMapClassFlip ∘ rootedStage (ℓ := ℓ) (n := n) := by
    funext p
    exact rootedStageWest_eq_flip_rootedStage p
  rw [hfun]
  have hflip : Measurable rootedFiniteDirectedMapClassFlip :=
    measurable_from_top
  have hstage : Measurable (rootedStage (ℓ := ℓ) (n := n)) :=
    measurable_of_countable _
  rw [← Measure.map_map hflip hstage]


/-- Helper toward Proposition 5.16. The west-rooted decorated sample is the
dart-flip image of the existing east-rooted decorated sample. -/
@[expose] noncomputable def rootedDecoratedWest {ℓ N : ℕ}
    (p : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} × Fin (ℓ - 1)) :
    RootedFiniteDirectedMapClass :=
  rootedFiniteDirectedMapClassFlip (rootedDecorated p)

/-- Helper toward Proposition 5.16. The decorated sample and west-rooted stage
are identified through the same left-endpoint equivalence as in
KMSWDiskRootedLaw. -/
theorem rootedDecoratedWest_eq_rootedStageWest (ℓ n : ℕ) (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    rootedDecoratedWest (kmswLeftEndpointSideEquiv ℓ n hℓ c, k) =
      rootedStageWest (c, k) := by
  unfold rootedDecoratedWest
  rw [rootedDecorated_eq_rootedStage hℓ c k]
  exact (rootedStageWest_eq_flip_rootedStage (c, k)).symm

/-- Helper toward Proposition 5.16. The west-rooted decorated mirror identity
is the dart-flip image of the established east-rooted mirror identity. -/
theorem rootedDecoratedWest_mirror {ℓ N : ℕ} (hℓ : 2 ≤ ℓ)
    (q : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled}) (k : Fin (ℓ - 1)) :
    rootedDecoratedWest (kmswMirrorSymmetryEquiv ℓ N hℓ q, Fin.rev k) =
      rootedFiniteDirectedMapClassFlip (rootedMirror (q, k)) := by
  unfold rootedDecoratedWest
  exact congrArg rootedFiniteDirectedMapClassFlip (rootedDecorated_mirror hℓ q k)

/-- Helper toward Proposition 5.16. The mirror of the stage with west root is
represented by the flipped rooted-stage mirror sample. -/
@[expose] noncomputable def rootedStageMirrorWest {ℓ n : ℕ}
    (p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1)) : RootedFiniteDirectedMapClass :=
  rootedFiniteDirectedMapClassFlip (rootedStageMirror p)

/-- Helper toward Proposition 5.16. The west-rooted walk-mirror identity
corresponds to the east-rooted mirror theorem after applying the same dart flip. -/
theorem rootedStageWest_walkMirror {ℓ n : ℕ} (hℓ : 2 ≤ ℓ)
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    rootedStageWest (kmswWalkMirrorEquiv ℓ n hℓ c, Fin.rev k) =
      rootedStageMirrorWest (c, k) := by
  rw [rootedStageWest_eq_flip_rootedStage, rootedStage_walkMirror]
  rfl

/-- Helper toward Proposition 5.16. The west-rooted joint law with the first-hit
time is the push-forward of the east-rooted joint law by dart flip on the rooted
map coordinate and identity on the hit-time coordinate. -/
theorem rootedStageWest_uniform_firstHit_eq_flip (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
        (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    letI : MeasurableSpace (RootedFiniteDirectedMapClass × ℕ) := ⊤
    ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map
      (fun p => (rootedStageWest p, kmswDiskFirstHit p.1 p.2)) =
    (((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map
      (fun p => (rootedStage p, kmswDiskFirstHit p.1 p.2))).map
        (fun z => (rootedFiniteDirectedMapClassFlip z.1, z.2)) := by
  letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
      (kmswLeftEndpointSideEquiv ℓ n hℓ)
  letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  letI : MeasurableSpace (RootedFiniteDirectedMapClass × ℕ) := ⊤
  have hfun :
      (fun p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1) =>
        (rootedStageWest p, kmswDiskFirstHit p.1 p.2)) =
      (fun z : RootedFiniteDirectedMapClass × ℕ =>
        (rootedFiniteDirectedMapClassFlip z.1, z.2)) ∘
      (fun p => (rootedStage p, kmswDiskFirstHit p.1 p.2)) := by
    funext p
    exact Prod.ext (rootedStageWest_eq_flip_rootedStage p) rfl
  rw [hfun]
  have houter : Measurable (fun z : RootedFiniteDirectedMapClass × ℕ =>
      (rootedFiniteDirectedMapClassFlip z.1, z.2)) := measurable_from_top
  have hinner : Measurable (fun p : KMSWLeftWalkClass ℓ n × Fin (ℓ - 1) =>
      (rootedStage p, kmswDiskFirstHit p.1 p.2)) := measurable_of_countable _
  rw [← Measure.map_map houter hinner]


/-- Helper toward Proposition 5.16. The west-rooted version of the mirrored
decorated sample is obtained by flipping its rooted class. -/
@[expose] noncomputable def rootedMirrorWest {ℓ N : ℕ}
    (p : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} × Fin (ℓ - 1)) :
    RootedFiniteDirectedMapClass :=
  rootedFiniteDirectedMapClassFlip (rootedMirror p)

/-- Helper toward Proposition 5.16. The uniform west-rooted decorated and
mirrored laws agree, as the established east-rooted mirror law remains valid
after applying the same class flip to both sides. -/
theorem rootedDecoratedWest_uniform_eq_rootedMirrorWest
    (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
        (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    ((uniformCountingMeasure
        {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedDecoratedWest =
    ((uniformCountingMeasure
        {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedMirrorWest := by
  letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
      (kmswLeftEndpointSideEquiv ℓ n hℓ)
  letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  have h := congrArg
    (fun μ => μ.map rootedFiniteDirectedMapClassFlip)
    (rootedDecorated_uniform_eq_rootedMirror ℓ n hℓ)
  have hflip : Measurable rootedFiniteDirectedMapClassFlip := measurable_from_top
  have hdecor : Measurable (rootedDecorated (ℓ := ℓ) (N := n + ℓ)) :=
    measurable_of_countable _
  have hmirror : Measurable (rootedMirror (ℓ := ℓ) (N := n + ℓ)) :=
    measurable_of_countable _
  rw [Measure.map_map hflip hdecor, Measure.map_map hflip hmirror] at h
  exact h


/-- Helper toward Proposition 5.16. The uniform law of the west-rooted
decorated sample agrees with the law of the west-rooted KMSW stage sample. -/
theorem rootedDecoratedWest_uniform_eq_rootedStageWest
    (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
        (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    ((uniformCountingMeasure
        {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled}).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedDecoratedWest =
    ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedStageWest := by
  letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
      (kmswLeftEndpointSideEquiv ℓ n hℓ)
  letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  have h := congrArg
    (fun μ => μ.map rootedFiniteDirectedMapClassFlip)
    (rootedDecorated_uniform_eq_rootedStage ℓ n hℓ)
  have hflip : Measurable rootedFiniteDirectedMapClassFlip := measurable_from_top
  have hdecor : Measurable (rootedDecorated (ℓ := ℓ) (N := n + ℓ)) :=
    measurable_of_countable _
  have hstage : Measurable (rootedStage (ℓ := ℓ) (n := n)) :=
    measurable_of_countable _
  rw [Measure.map_map hflip hdecor, Measure.map_map hflip hstage] at h
  have hfunDecorated : rootedDecoratedWest (ℓ := ℓ) (N := n + ℓ) =
      rootedFiniteDirectedMapClassFlip ∘ rootedDecorated (ℓ := ℓ) (N := n + ℓ) := by
    funext p
    rfl
  have hfunStage : rootedStageWest (ℓ := ℓ) (n := n) =
      rootedFiniteDirectedMapClassFlip ∘ rootedStage (ℓ := ℓ) (n := n) := by
    funext p
    exact rootedStageWest_eq_flip_rootedStage p
  rw [hfunDecorated, hfunStage]
  exact h

/-- Helper toward Proposition 5.16. The uniform west-rooted stage and
west-rooted mirrored-stage laws agree. -/
theorem rootedStageWest_uniform_eq_rootedStageMirrorWest
    (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) :
    letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
      Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
        (kmswLeftEndpointSideEquiv ℓ n hℓ)
    letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
    letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
    letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
    ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedStageWest =
    ((uniformCountingMeasure (KMSWLeftWalkClass ℓ n)).prod
      (uniformCountingMeasure (Fin (ℓ - 1)))).map rootedStageMirrorWest := by
  letI : Fintype {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} :=
    Fintype.ofEquiv (KMSWLeftWalkClass ℓ n)
      (kmswLeftEndpointSideEquiv ℓ n hℓ)
  letI : MeasurableSpace (KMSWLeftWalkClass ℓ n) := ⊤
  letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsChanneled} := ⊤
  letI : MeasurableSpace (Fin (ℓ - 1)) := ⊤
  letI : MeasurableSpace RootedFiniteDirectedMapClass := ⊤
  have h := congrArg
    (fun μ => μ.map rootedFiniteDirectedMapClassFlip)
    (rootedStage_uniform_eq_rootedStageMirror ℓ n hℓ)
  have hflip : Measurable rootedFiniteDirectedMapClassFlip := measurable_from_top
  have hstage : Measurable (rootedStage (ℓ := ℓ) (n := n)) :=
    measurable_of_countable _
  have hmirror : Measurable (rootedStageMirror (ℓ := ℓ) (n := n)) :=
    measurable_of_countable _
  rw [Measure.map_map hflip hstage, Measure.map_map hflip hmirror] at h
  have hfunStage : rootedStageWest (ℓ := ℓ) (n := n) =
      rootedFiniteDirectedMapClassFlip ∘ rootedStage (ℓ := ℓ) (n := n) := by
    funext p
    exact rootedStageWest_eq_flip_rootedStage p
  have hfunMirror : rootedStageMirrorWest (ℓ := ℓ) (n := n) =
      rootedFiniteDirectedMapClassFlip ∘ rootedStageMirror (ℓ := ℓ) (n := n) := by
    funext p
    rfl
  rw [hfunStage, hfunMirror]
  exact h



end DirectedDistances.PaperProofs.Section5
