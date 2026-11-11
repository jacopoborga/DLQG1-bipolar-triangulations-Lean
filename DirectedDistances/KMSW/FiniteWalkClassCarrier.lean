/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FiniteWalkClassMap
public import DirectedDistances.PaperProofs.Section3.KMSWBdyOuterFace
public import DirectedDistances.PlanarMap.GeneralBipolarBoundary

/-! # Finite walk classes in the base boundary carrier

Helpers toward `thm-kmsw` (forward membership); not the paper result
single-edge walk at `(ℓ,r,n) = (1,1,1)` is excluded from the strong carrier. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
Every dart of a finite cone-walk stage is present, by the boundary count -/
theorem kmswWalkClassBase_noMissingDarts {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    ∀ d : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge,
      ¬ (kmswStageDirectedMap (codeExtend c) (n - 1)).missing d := by
  have h := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnoMissing,
    _, _, _⟩
  exact hnoMissing

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The finite stage map is planar (`def-kmsw`, -/
theorem kmswWalkClassBase_planar {ℓ r n : ℕ} (c : KMSWWalkClass ℓ r n) :
    (kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.IsPlanar := by
  rw [kmswStageDirectedMap_toCombinatorialMap]
  exact kmswMap_isPlanar (codeExtend c) (n - 1)

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The stage orientation is acyclic by its rational vertex rank -/
theorem kmswWalkClassBase_acyclic {ℓ r n : ℕ} (c : KMSWWalkClass ℓ r n) :
    (kmswStageDirectedMap (codeExtend c) (n - 1)).IsAcyclic :=
  kmswStageDirectedMap_isAcyclic (codeExtend c) (n - 1)

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
Every non-outer dart belongs to a created triangular face -/
theorem kmswWalkClassBase_innerFacesDegreeThree {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) :
    ∀ d, ¬ (kmswStageDirectedMap (codeExtend c) (n - 1)).IsOuter d →
      (kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.faceSucc
          ((kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.faceSucc
            ((kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.faceSucc d)) = d ∧
        (kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.faceSucc d ≠ d ∧
        (kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.faceSucc
          ((kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.faceSucc d) ≠ d := by
  rw [kmswStageDirectedMap_toCombinatorialMap (codeExtend c) (n - 1)]
  intro d houter
  let w := codeExtend c
  let m := n - 1
  obtain hboundary | ⟨j, ⟨hjn, htriangle⟩, _⟩ := stage_dart_partition w m d
  · exact (houter ((kmsw_bdy_source_four_arcs w m).1.1.1 d hboundary)).elim
  · have htyped : d = stageTriangleDart₁ w m j hjn ∨
        d = stageTriangleDart₂ w m j hjn ∨ d = stageTriangleDart₃ w m j hjn := by
      rcases d with ⟨e, b⟩
      simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false]
        at htriangle
      rcases htriangle with htriangle | htriangle | htriangle
      · left
        apply Prod.ext
        · apply Fin.ext
          simpa only [stageTriangleDart₁, stageTriangleDartAt] using
            congrArg Prod.fst htriangle
        · simpa only [stageTriangleDart₁, stageTriangleDartAt] using
            congrArg Prod.snd htriangle
      · right
        left
        apply Prod.ext
        · apply Fin.ext
          simpa only [stageTriangleDart₂, stageTriangleDartAt] using
            congrArg Prod.fst htriangle
        · simpa only [stageTriangleDart₂, stageTriangleDartAt] using
            congrArg Prod.snd htriangle
      · right
        right
        apply Prod.ext
        · apply Fin.ext
          simpa only [stageTriangleDart₃, stageTriangleDartAt] using
            congrArg Prod.fst htriangle
        · simpa only [stageTriangleDart₃, stageTriangleDartAt] using
            congrArg Prod.snd htriangle
    have hface := stageTriangle_isFace w j m hjn
    have hface' : FaceSucc3Cycle (kmswMap w m).faceSucc
        (stageTriangleDart₁ w m j hjn) (stageTriangleDart₂ w m j hjn)
        (stageTriangleDart₃ w m j hjn) := hface
    rcases hface' with ⟨hab, hbc, hca, habne, hbcne, hcane⟩
    dsimp only [w, m] at hab hbc hca habne hbcne hcane
    let f := (kmswMap (codeExtend c) (n - 1)).faceSucc
    change f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn) =
        stageTriangleDart₂ (codeExtend c) (n - 1) j hjn at hab
    change f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn) =
        stageTriangleDart₃ (codeExtend c) (n - 1) j hjn at hbc
    change f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn) =
        stageTriangleDart₁ (codeExtend c) (n - 1) j hjn at hca
    change stageTriangleDart₁ (codeExtend c) (n - 1) j hjn ≠
        stageTriangleDart₂ (codeExtend c) (n - 1) j hjn at habne
    change stageTriangleDart₂ (codeExtend c) (n - 1) j hjn ≠
        stageTriangleDart₃ (codeExtend c) (n - 1) j hjn at hbcne
    change stageTriangleDart₃ (codeExtend c) (n - 1) j hjn ≠
        stageTriangleDart₁ (codeExtend c) (n - 1) j hjn at hcane
    rcases htyped with h | h | h
    · subst d
      change f (f (f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn))) =
          stageTriangleDart₁ (codeExtend c) (n - 1) j hjn ∧
        f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn) ≠
          stageTriangleDart₁ (codeExtend c) (n - 1) j hjn ∧
        f (f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn)) ≠
          stageTriangleDart₁ (codeExtend c) (n - 1) j hjn
      refine ⟨?_, ?_, ?_⟩
      · calc
          f (f (f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn))) =
              f (f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn)) :=
                congrArg f (congrArg f hab)
          _ = f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn) :=
                congrArg f hbc
          _ = stageTriangleDart₁ (codeExtend c) (n - 1) j hjn := hca
      · intro heq
        exact habne (by
          calc
            stageTriangleDart₁ (codeExtend c) (n - 1) j hjn =
                f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn) := heq.symm
            _ = stageTriangleDart₂ (codeExtend c) (n - 1) j hjn := hab)
      · intro heq
        exact hcane (by
          calc
            stageTriangleDart₃ (codeExtend c) (n - 1) j hjn =
                f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn) := hbc.symm
            _ = f (f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn)) :=
                (congrArg f hab).symm
            _ = stageTriangleDart₁ (codeExtend c) (n - 1) j hjn := heq)
    · subst d
      change f (f (f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn))) =
          stageTriangleDart₂ (codeExtend c) (n - 1) j hjn ∧
        f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn) ≠
          stageTriangleDart₂ (codeExtend c) (n - 1) j hjn ∧
        f (f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn)) ≠
          stageTriangleDart₂ (codeExtend c) (n - 1) j hjn
      refine ⟨?_, ?_, ?_⟩
      · calc
          f (f (f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn))) =
              f (f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn)) :=
                congrArg f (congrArg f hbc)
          _ = f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn) :=
                congrArg f hca
          _ = stageTriangleDart₂ (codeExtend c) (n - 1) j hjn := hab
      · intro heq
        exact hbcne (by
          calc
            stageTriangleDart₂ (codeExtend c) (n - 1) j hjn =
                f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn) := heq.symm
            _ = stageTriangleDart₃ (codeExtend c) (n - 1) j hjn := hbc)
      · intro heq
        exact habne (by
          calc
            stageTriangleDart₁ (codeExtend c) (n - 1) j hjn =
                f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn) := hca.symm
            _ = f (f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn)) :=
                (congrArg f hbc).symm
            _ = stageTriangleDart₂ (codeExtend c) (n - 1) j hjn := heq)
    · subst d
      change f (f (f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn))) =
          stageTriangleDart₃ (codeExtend c) (n - 1) j hjn ∧
        f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn) ≠
          stageTriangleDart₃ (codeExtend c) (n - 1) j hjn ∧
        f (f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn)) ≠
          stageTriangleDart₃ (codeExtend c) (n - 1) j hjn
      refine ⟨?_, ?_, ?_⟩
      · calc
          f (f (f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn))) =
              f (f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn)) :=
                congrArg f (congrArg f hca)
          _ = f (stageTriangleDart₂ (codeExtend c) (n - 1) j hjn) :=
                congrArg f hab
          _ = stageTriangleDart₃ (codeExtend c) (n - 1) j hjn := hbc
      · intro heq
        exact hcane (by
          calc
            stageTriangleDart₃ (codeExtend c) (n - 1) j hjn =
                f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn) := heq.symm
            _ = stageTriangleDart₁ (codeExtend c) (n - 1) j hjn := hca)
      · intro heq
        exact hbcne (by
          calc
            stageTriangleDart₂ (codeExtend c) (n - 1) j hjn =
                f (stageTriangleDart₁ (codeExtend c) (n - 1) j hjn) := hab.symm
            _ = f (f (stageTriangleDart₃ (codeExtend c) (n - 1) j hjn)) :=
                (congrArg f hca).symm
            _ = stageTriangleDart₃ (codeExtend c) (n - 1) j hjn := heq)

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The source candidate is the tail vertex of the first UL dart in outer-face -/
@[expose] def kmswWalkClassBaseSource {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) :
    MapVertex (kmswStageDirectedMap (codeExtend c) (n - 1)) :=
  dartTailVertex (kmswStageDirectedMap (codeExtend c) (n - 1))
    (stageULHeadDart (codeExtend c) (n - 1))

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The sink candidate is the tail vertex of the first LR outer dart, equivalently
the terminal vertex of the directed LR boundary run (`thm-kmsw`, -/
@[expose] def kmswWalkClassBaseSink {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) :
    MapVertex (kmswStageDirectedMap (codeExtend c) (n - 1)) := by
  let w := codeExtend c
  let m := n - 1
  have hLR : (kmswStage w m).LR ≠ [] := kmswStage_LR_nonempty w m
  have hrun : kmswStageLRDartRun w m ≠ [] := by
    intro hnil
    have hlen : (kmswStageLRDartRun w m).length = (kmswStage w m).LR.length := by
      simp [kmswStageLRDartRun, stageDarts]
    rw [hnil] at hlen
    exact hLR (List.length_eq_zero_iff.mp hlen.symm)
  exact dartTailVertex (kmswStageDirectedMap w m)
    ((kmswStageLRDartRun w m).head hrun)

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The four-arc witness for the finite walk stage has exactly its UL and LR
present runs; its UR and LL runs are empty (`thm-kmsw`, -/
theorem kmswWalkClassBase_outerFourArcs {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    FourArcsWitness (kmswStageDirectedMap (codeExtend c) (n - 1))
      (stageOuterNonemptyWord (codeExtend c) (n - 1))
      (kmswStageULDartRun (codeExtend c) (n - 1)) []
      (kmswStageLRDartRun (codeExtend c) (n - 1)) [] := by
  have h := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hURnil, hLLnil,
    _, _, _, _, _⟩
  have hUR : kmswStageURDartRun (codeExtend c) (n - 1) = [] := by
    simp [kmswStageURDartRun, stageDarts, hURnil]
  have hLL : kmswStageLLDartRun (codeExtend c) (n - 1) = [] := by
    simp [kmswStageLLDartRun, stageDarts, hLLnil]
  simpa only [hUR, hLL] using
    (kmsw_bdy_source_four_arcs (codeExtend c) (n - 1)).1

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The finite walk stage has positive UL boundary length (`thm-kmsw`, -/
theorem kmswWalkClassBase_leftLengthPos {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) : 1 ≤ ℓ := by
  have h := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at h
  exact h.1

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The finite walk stage has positive LR boundary length (`thm-kmsw`, -/
theorem kmswWalkClassBase_rightLengthPos {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) : 1 ≤ r := by
  have h := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at h
  exact h.2.1

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The UL dart run has the source walk's left length (`thm-kmsw`, -/
theorem kmswWalkClassBase_leftDartRun_length {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (kmswStageULDartRun (codeExtend c) (n - 1)).length = ℓ := by
  have h := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, hUL, _, _, _, _, _, _, _, _, _, _⟩
  simpa [kmswStageULDartRun, stageDarts] using hUL

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The reversed LR dart run has the source walk's right length (`thm-kmsw`, -/
theorem kmswWalkClassBase_rightDartRun_length {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (kmswStageLRDartRun (codeExtend c) (n - 1)).length = r := by
  have h := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hLR, _, _, _, _, _, _, _, _, _⟩
  simpa [kmswStageLRDartRun, stageDarts] using hLR

private theorem avoid_new_endpoint (f : ℕ → ℕ) (E b v : ℕ) :
    (∀ e < E + 1, (if e = E then b else f e) ≠ v) ↔
      (∀ e < E, f e ≠ v) ∧ b ≠ v := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro e he
      simpa [show e ≠ E by omega] using h e (by omega)
    · simpa using h E (by omega)
  · rintro ⟨h, hb⟩ e he
    split_ifs with hEq
    · exact hb
    · exact h e (by omega)

private theorem start_transfer (s t : State) (es : List ℕ)
    (h : ∀ e ∈ es, t.west e = s.west e) :
    boundaryStart t es = boundaryStart s es := by
  cases es with
  | nil => rfl
  | cons e es => simp [boundaryStart, h e (by simp)]

private theorem end_transfer (s t : State) (es : List ℕ)
    (h : ∀ e ∈ es, t.east e = s.east e) :
    boundaryEnd t es = boundaryEnd s es := by
  unfold boundaryEnd
  cases hh : es.getLast? with
  | none => rfl
  | some e =>
    have he : e ∈ es := List.mem_of_mem_getLast? (by simp [hh])
    simp only [Option.map_some, h e he]

private theorem stage_allocated_poles (w : ℕ → Fin 3) (m : ℕ) :
    (∀ v, (∀ e < (kmswStage w m).nextEdge, (kmswStage w m).east e ≠ v) ↔
      (kmswStage w m).nextVertex ≤ v ∨
        boundaryStart (kmswStage w m) (kmswStage w m).UL = some v) ∧
    (∀ v, (∀ e < (kmswStage w m).nextEdge, (kmswStage w m).west e ≠ v) ↔
      (kmswStage w m).nextVertex ≤ v ∨
        boundaryEnd (kmswStage w m) (kmswStage w m).LR = some v) := by
  induction m with
  | zero =>
    simp only [kmswStage, kmswInit, boundaryStart, boundaryEnd,
      List.head?_cons, List.getLast?_singleton, Option.map_some]
    constructor <;> intro v <;> simp <;> omega
  | succ m ih =>
    let s := kmswStage w m
    change (∀ v, (∀ e < s.nextEdge, s.east e ≠ v) ↔
      s.nextVertex ≤ v ∨ boundaryStart s s.UL = some v) ∧
      (∀ v, (∀ e < s.nextEdge, s.west e ≠ v) ↔
      s.nextVertex ≤ v ∨ boundaryEnd s s.LR = some v) at ih
    have ha : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w m).1
    have hends : ∀ e < s.nextEdge, s.west e < s.nextVertex ∧
        s.east e < s.nextVertex := kmswStage_endpoints_lt_nextVertex w m
    have hids : ∀ e ∈ s.UL ++ s.UR ++ s.LL ++ s.LR, e < s.nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge w m).2
    have hu : ∀ e ∈ s.UL, e < s.nextEdge := by
      intro e he
      exact hids e (by simp only [List.mem_append]; tauto)
    have hl : ∀ e ∈ s.LR, e < s.nextEdge := by
      intro e he
      exact hids e (by simp only [List.mem_append]; tauto)
    have hLR : s.LR ≠ [] := kmswStage_LR_nonempty w m
    have hstartBound : ∀ v, boundaryStart s s.UL = some v → v < s.nextVertex := by
      intro v hv
      cases hh : s.UL with
      | nil => simp [boundaryStart, hh] at hv
      | cons e es =>
        have he : e < s.nextEdge := hu e (by simp [hh])
        have hv' : s.west e = v := by simpa [boundaryStart, hh] using hv
        exact hv' ▸ (hends e he).1
    have hendBound : ∀ v, boundaryEnd s s.LR = some v → v < s.nextVertex := by
      intro v hv
      have he : s.LR.getLast hLR ∈ s.LR := List.getLast_mem hLR
      have hv' : s.east (s.LR.getLast hLR) = v := by
        simpa [boundaryEnd, List.getLast?_eq_getLast_of_ne_nil hLR] using hv
      exact hv' ▸ (hends _ (hl _ he)).2
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
    change s.UL = xs ++ [s.active] at hxs
    have hsi : ∀ e < s.nextEdge, boundaryStart s s.UL ≠ some (s.east e) := by
      intro e he hs
      have hn := (ih.1 (s.east e)).2 (Or.inr hs)
      exact hn e he rfl
    have hso : ∀ e < s.nextEdge, boundaryEnd s s.LR ≠ some (s.west e) := by
      intro e he hs
      have hn := (ih.2 (s.west e)).2 (Or.inr hs)
      exact hn e he rfl
    have oldStart (t : State) (h : ∀ e < s.nextEdge, t.west e = s.west e) :
        boundaryStart t s.UL = boundaryStart s s.UL :=
      start_transfer s t s.UL (fun e he => h e (hu e he))
    have oldEnd (t : State) (h : ∀ e < s.nextEdge, t.east e = s.east e) :
        boundaryEnd t s.LR = boundaryEnd s s.LR :=
      end_transfer s t s.LR (fun e he => h e (hl e he))
    by_cases hc : w m = 0
    · have hn : kmswStage w (m + 1) = kmswStepOfStep s .left := by
        simp only [kmswStage, kmswStep, hc, kmswCodeStep, ↓reduceIte]; rfl
      rw [hn]
      cases hp : s.UL.dropLast.reverse with
      | nil =>
        have hxnil : xs = [] := by
          rw [hxs] at hp
          simpa using hp
        have hus : s.UL = [s.active] := by simpa [hxnil] using hxs
        have hstart : boundaryStart s s.UL = some (s.west s.active) := by
          simp [boundaryStart, hus]
        let t := kmswStepOfStep s .left
        have htend : boundaryEnd t t.LR = boundaryEnd s s.LR := by
          rw [show t.LR = s.LR by simp [t, kmswStepOfStep, hp, State.addEdge]]
          apply oldEnd
          intro e he
          simp [t, kmswStepOfStep, hp, State.addEdge,
            show e ≠ s.nextEdge by omega, show e ≠ s.nextEdge + 1 by omega]
        have htstart : boundaryStart t t.UL = some s.nextVertex := by
          simp [t, kmswStepOfStep, hp, boundaryStart, State.addEdge]
        change (∀ v, _ ↔ _ ∨ boundaryStart t t.UL = some v) ∧
          (∀ v, _ ↔ _ ∨ boundaryEnd t t.LR = some v)
        rw [htstart, htend]
        simp only [kmswStepOfStep, hp]
        dsimp only [State.addEdge]
        simp only [avoid_new_endpoint]
        constructor <;> intro v
        · rw [ih.1 v, hstart]
          have hb := hends s.active ha
          simp only [Option.some.injEq]
          omega
        · rw [ih.2 v]
          have hb := hendBound v
          grind
      | cons e es =>
        have hx : xs = es.reverse ++ [e] := by
          rw [hxs] at hp
          simpa using congrArg List.reverse hp
        have hus : s.UL = es.reverse ++ [e, s.active] := by
          rw [hxs, hx]; simp only [List.append_assoc, List.singleton_append]
        have he : e < s.nextEdge := hu e (by simp [hus])
        let t := kmswStepOfStep s .left
        have holdW : ∀ f < s.nextEdge, t.west f = s.west f := by
          intro f hf
          simp [t, kmswStepOfStep, hp, State.addEdge, show f ≠ s.nextEdge by omega]
        have htend : boundaryEnd t t.LR = boundaryEnd s s.LR := by
          rw [show t.LR = s.LR by simp [t, kmswStepOfStep, hp, State.addEdge]]
          apply oldEnd
          intro f hf
          simp [t, kmswStepOfStep, hp, State.addEdge, show f ≠ s.nextEdge by omega]
        have htstart : boundaryStart t t.UL = boundaryStart s s.UL := by
          have htu : t.UL = es.reverse ++ [s.nextEdge] := by simp [t, kmswStepOfStep, hp]
          rw [htu, hus]
          cases hr : es.reverse with
          | nil => simp [boundaryStart, t, kmswStepOfStep, hp, State.addEdge, hr]
          | cons f fs =>
            have hf : f < s.nextEdge := hu f (by simp [hus, hr])
            simp [boundaryStart, holdW f hf]
        change (∀ v, _ ↔ _ ∨ boundaryStart t t.UL = some v) ∧
          (∀ v, _ ↔ _ ∨ boundaryEnd t t.LR = some v)
        rw [htstart, htend]
        simp only [kmswStepOfStep, hp]
        dsimp only [State.addEdge]
        simp only [avoid_new_endpoint]
        constructor <;> intro v
        · rw [ih.1 v]
          have hb := (hends s.active ha).2
          have hs := hsi s.active ha
          grind
        · rw [ih.2 v]
          have hb := (hends e he).1
          have hs := hso e he
          grind
    · by_cases hc1 : w m = 1
      · have hn : kmswStage w (m + 1) = kmswStepOfStep s .up := by
          simp [kmswStage, kmswStep, kmswCodeStep, hc1, s]
        rw [hn]
        let t := kmswStepOfStep s .up
        have holdW : ∀ f < s.nextEdge, t.west f = s.west f := by
          intro f hf
          simp [t, kmswStepOfStep, State.addEdge,
            show f ≠ s.nextEdge by omega, show f ≠ s.nextEdge + 1 by omega]
        have htstart : boundaryStart t t.UL = boundaryStart s s.UL := by
          have htu : t.UL = xs ++ [s.nextEdge] := by simp [t, kmswStepOfStep, hxs]
          rw [htu, hxs]
          cases hx : xs with
          | nil => simp [boundaryStart, t, kmswStepOfStep, State.addEdge]
          | cons f fs =>
            have hf : f < s.nextEdge := hu f (by simp [hxs, hx])
            simp [boundaryStart, holdW f hf]
        have htend : boundaryEnd t t.LR = boundaryEnd s s.LR := by
          change boundaryEnd t s.LR = _
          apply oldEnd
          intro f hf
          simp [t, kmswStepOfStep, State.addEdge,
            show f ≠ s.nextEdge by omega, show f ≠ s.nextEdge + 1 by omega]
        change (∀ v, _ ↔ _ ∨ boundaryStart t t.UL = some v) ∧
          (∀ v, _ ↔ _ ∨ boundaryEnd t t.LR = some v)
        rw [htstart, htend]
        dsimp only [kmswStepOfStep, State.addEdge]
        simp only [avoid_new_endpoint]
        constructor <;> intro v
        · rw [ih.1 v]
          have hb := (hends s.active ha).2
          have hs := hsi s.active ha
          grind
        · rw [ih.2 v]
          have hb := (hends s.active ha).1
          have hs := hso s.active ha
          grind
      · have hc2 : w m = 2 := by
          have hlt := (w m).isLt
          have h0 : (w m).val ≠ 0 := fun h => hc (Fin.ext h)
          have h1 : (w m).val ≠ 1 := fun h => hc1 (Fin.ext h)
          exact Fin.ext (by omega)
        have hn : kmswStage w (m + 1) = kmswStepOfStep s .down := by
          simp [kmswStage, kmswStep, kmswCodeStep, hc2, s]
        rw [hn]
        cases hr : s.UR with
        | nil =>
          let t := kmswStepOfStep s .down
          have holdW : ∀ f < s.nextEdge, t.west f = s.west f := by
            intro f hf
            simp [t, kmswStepOfStep, hr, State.addEdge, show f ≠ s.nextEdge by omega]
          have htstart : boundaryStart t t.UL = boundaryStart s s.UL := by
            have htu : t.UL = s.UL ++ [s.nextEdge] := by simp [t, kmswStepOfStep, hr]
            rw [htu]
            have hu0 : s.UL ≠ [] := by rw [hxs]; simp
            simp only [boundaryStart, List.head?_append_of_ne_nil _ hu0]
            exact oldStart t holdW
          have htend : boundaryEnd t t.LR = some s.nextVertex := by
            simp [t, kmswStepOfStep, hr, boundaryEnd, State.addEdge]
          have hend : boundaryEnd s s.LR = some (s.east s.active) := by
            have hh := (kmswStage_boundary_chain_invariant w m).2.2.2.2.2.2 hLR hr
            simp only [boundaryEnd, List.getLast?_eq_getLast_of_ne_nil hLR, Option.map_some]
            exact congrArg some hh.symm
          change (∀ v, _ ↔ _ ∨ boundaryStart t t.UL = some v) ∧
            (∀ v, _ ↔ _ ∨ boundaryEnd t t.LR = some v)
          rw [htstart, htend]
          simp only [kmswStepOfStep, hr]
          dsimp only [State.addEdge]
          simp only [avoid_new_endpoint]
          constructor <;> intro v
          · rw [ih.1 v]
            have hb := hstartBound v
            grind
          · rw [ih.2 v, hend]
            have hb := (hends s.active ha).2
            simp only [Option.some.injEq]
            omega
        | cons e es =>
          have hu0 : s.UL ≠ [] := by rw [hxs]; simp
          simp only [kmswStepOfStep, hr]
          constructor
          · intro v
            simpa only [boundaryStart, List.head?_append_of_ne_nil _ hu0] using ih.1 v
          · exact ih.2

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
Allocated geometric edges, including missing edges, characterize the two
boundary poles at every stage (`def-kmsw`, -/
theorem kmswStage_allocated_poles (w : ℕ → Fin 3) (m : ℕ) :
    (∀ v < (kmswStage w m).nextVertex,
      (∀ e < (kmswStage w m).nextEdge, (kmswStage w m).east e ≠ v) ↔
        boundaryStart (kmswStage w m) (kmswStage w m).UL = some v) ∧
    (∀ v < (kmswStage w m).nextVertex,
      (∀ e < (kmswStage w m).nextEdge, (kmswStage w m).west e ≠ v) ↔
        boundaryEnd (kmswStage w m) (kmswStage w m).LR = some v) := by
  constructor
  · intro v hv
    simpa only [show ¬ (kmswStage w m).nextVertex ≤ v by omega, false_or]
      using (stage_allocated_poles w m).1 v
  · intro v hv
    simpa only [show ¬ (kmswStage w m).nextVertex ≤ v by omega, false_or]
      using (stage_allocated_poles w m).2 v

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The final admissible stage has exactly the designated source and sink -/
theorem kmswWalkClassBase_poles {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    let M := kmswStageDirectedMap (codeExtend c) (n - 1)
    let S := kmswWalkClassBaseSource c
    let T := kmswWalkClassBaseSink c
    (¬ ∃ u, M.directedStep u S) ∧
    (∀ v, (¬ ∃ u, M.directedStep u v) → v = S) ∧
    (¬ ∃ v, M.directedStep T v) ∧
    (∀ v, (¬ ∃ u, M.directedStep v u) → v = T) := by
  classical
  let w := codeExtend c
  let m := n - 1
  let s := kmswStage w m
  let M := kmswStageDirectedMap w m
  let E := stageVertexEquiv w m
  let S := kmswWalkClassBaseSource c
  let T := kmswWalkClassBaseSink c
  have hpres (e : Fin s.nextEdge) : s.present e.val = true := by
    have h := kmswWalkClassBase_noMissingDarts hn c (e, false)
    change ¬ s.present e.val = false at h
    cases hh : s.present e.val with
    | false => exact (h hh).elim
    | true => rfl
  have hUL : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last w m).1
  have hLR : s.LR ≠ [] := kmswStage_LR_nonempty w m
  have hS : boundaryStart s s.UL = some (E S).val := by
    simp only [boundaryStart, List.head?_eq_some_head hUL, Option.map_some]
    rfl
  have hT : boundaryEnd s s.LR = some (E T).val := by
    simp only [boundaryEnd, List.getLast?_eq_getLast_of_ne_nil hLR, Option.map_some]
    change some (s.east (s.LR.getLast hLR)) =
      some (stageEndpoint s ((kmswStageLRDartRun w m).head _))
    simp only [kmswStageLRDartRun, stageDarts, List.head_map, List.head_attach,
      stageEndpoint, List.head_reverse, ↓reduceIte]
    rfl
  have hin (v : MapVertex M) :
      (¬ ∃ u, M.directedStep u v) ↔ boundaryStart s s.UL = some (E v).val := by
    rw [← (kmswStage_allocated_poles w m).1 (E v).val (E v).isLt]
    constructor
    · intro h e he heq
      let d : StageDart s.nextEdge := (⟨e, he⟩, false)
      apply h
      refine ⟨dartTailVertex M d, d, kmswWalkClassBase_noMissingDarts hn c d,
        ⟨hpres ⟨e, he⟩, rfl⟩, rfl, ?_⟩
      apply E.injective
      apply Fin.ext
      change s.east e = (E v).val
      exact heq
    · intro h ⟨u, d, _, ht, _, hv⟩
      have hh := congrArg (fun a => (E a).val) hv
      change stageEndpoint s (edgeFlip s.nextEdge d) = (E v).val at hh
      have hEq : s.east d.1.val = (E v).val := by
        simpa [stageEndpoint, edgeFlip, ht.2] using hh
      exact h d.1.val d.1.isLt hEq
  have hout (v : MapVertex M) :
      (¬ ∃ u, M.directedStep v u) ↔ boundaryEnd s s.LR = some (E v).val := by
    rw [← (kmswStage_allocated_poles w m).2 (E v).val (E v).isLt]
    constructor
    · intro h e he heq
      let d : StageDart s.nextEdge := (⟨e, he⟩, false)
      apply h
      refine ⟨dartHeadVertex M d, d, kmswWalkClassBase_noMissingDarts hn c d,
        ⟨hpres ⟨e, he⟩, rfl⟩, ?_, rfl⟩
      apply E.injective
      apply Fin.ext
      change s.west e = (E v).val
      exact heq
    · intro h ⟨u, d, _, ht, hv, _⟩
      have hh := congrArg (fun a => (E a).val) hv
      change stageEndpoint s d = (E v).val at hh
      have hEq : s.west d.1.val = (E v).val := by
        simpa [stageEndpoint, ht.2] using hh
      exact h d.1.val d.1.isLt hEq
  refine ⟨(hin S).2 hS, ?_, (hout T).2 hT, ?_⟩
  · intro v hv
    apply E.injective
    apply Fin.ext
    exact (Option.some.inj (hS.symm.trans ((hin v).1 hv))).symm
  · intro v hv
    apply E.injective
    apply Fin.ext
    exact (Option.some.inj (hT.symm.trans ((hout v).1 hv))).symm

private def simplePathOfDartChain {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (ha : M.IsAcyclic)
    (ds : List D) (hne : ds ≠ [])
    (hp : ∀ d ∈ ds, ¬ M.missing d ∧ M.tail d)
    (hc : ds.IsChain (fun d e => dartHeadVertex M d = dartTailVertex M e)) :
    SimpleDirectedDartPath M (dartTailVertex M (ds.head hne))
      (dartHeadVertex M (ds.getLast hne)) ds.length := by
  let vs := ds.map (dartTailVertex M) ++ [dartHeadVertex M (ds.getLast hne)]
  have hvlen : vs.length = ds.length + 1 := by simp [vs]
  have hs : ∀ i (hi : i < ds.length),
      vs[i]'(by omega) = dartTailVertex M ds[i] ∧
      vs[i + 1]'(by omega) = dartHeadVertex M ds[i] := by
    intro i hi
    constructor
    · dsimp only [vs]
      rw [List.getElem_append_left (by simpa using hi), List.getElem_map]
    · by_cases hn : i + 1 < ds.length
      · dsimp only [vs]
        rw [List.getElem_append_left (by simpa using hn), List.getElem_map]
        exact ((List.isChain_iff_getElem.mp hc) i hn).symm
      · have he : i + 1 = ds.length := by omega
        have hi' : ds.length - 1 = i := by omega
        dsimp only [vs]
        rw [List.getElem_append_right (by simp only [List.length_map]; omega)]
        simp only [List.length_map, he, Nat.sub_self, List.getElem_cons_zero]
        simp only [List.getLast_eq_getElem, hi']
  have hchain : vs.IsChain M.directedStep := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have hid : i < ds.length := by omega
    have hpp := hp ds[i] (List.getElem_mem hid)
    refine ⟨ds[i], hpp.1, hpp.2, (hs i hid).1.symm, (hs i hid).2.symm⟩
  have htrans : vs.Pairwise (Relation.TransGen M.directedStep) := by
    apply List.isChain_iff_pairwise.mp
    exact hchain.imp (fun _ _ h => Relation.TransGen.single h)
  have hnodup : vs.Nodup := by
    apply htrans.imp
    intro a b hab heq
    subst b
    exact ha a hab
  refine {
    darts := ds
    vertices := vs
    darts_length := rfl
    vertices_length := hvlen
    vertices_nodup := hnodup
    start_vertex := ?_
    end_vertex := ?_
    edge_step := ?_ }
  · change vs[0]'_ = _
    rw [(hs 0 (List.length_pos_iff.mpr hne)).1]
    congr 1
    exact List.getElem_zero _
  · change vs[ds.length]'_ = _
    dsimp only [vs]
    rw [List.getElem_append_right (by simp)]
    simp
  · intro i
    exact ⟨(hp (ds.get i) (List.get_mem ds i)).1,
      (hp (ds.get i) (List.get_mem ds i)).2, (hs i.val i.isLt).1,
      (hs i.val i.isLt).2⟩

private noncomputable def stageSimplePath {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) (es : List ℕ)
    (hb : ∀ e ∈ es, e < (kmswStage (codeExtend c) (n - 1)).nextEdge)
    (hne : es ≠ []) (hc : WestEastChain (kmswStage (codeExtend c) (n - 1)) es)
    (S T : MapVertex (kmswStageDirectedMap (codeExtend c) (n - 1)))
    (hS : boundaryStart (kmswStage (codeExtend c) (n - 1)) es =
      some ((stageVertexEquiv (codeExtend c) (n - 1)) S).val)
    (hT : boundaryEnd (kmswStage (codeExtend c) (n - 1)) es =
      some ((stageVertexEquiv (codeExtend c) (n - 1)) T).val)
    (k : ℕ) (hlen : es.length = k) :
    SimpleDirectedDartPath (kmswStageDirectedMap (codeExtend c) (n - 1)) S T k := by
  let w := codeExtend c
  let m := n - 1
  let s := kmswStage w m
  let M := kmswStageDirectedMap w m
  let E := stageVertexEquiv w m
  let ds := stageDarts s es false hb
  have hds : ds ≠ [] := by simpa [ds, stageDarts] using hne
  have hdlen : ds.length = k := by simpa [ds, stageDarts] using hlen
  have hchain : ds.IsChain (fun d e => dartHeadVertex M d = dartTailVertex M e) := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    apply E.injective
    apply Fin.ext
    change stageEndpoint s (edgeFlip s.nextEdge ds[i]) = stageEndpoint s ds[i + 1]
    simp only [ds, stageDarts, List.getElem_map, List.getElem_attach,
      stageEndpoint, edgeFlip]
    exact (List.isChain_iff_getElem.mp hc) i (by simpa [ds, stageDarts] using hi)
  have hp : ∀ d ∈ ds, ¬ M.missing d ∧ M.tail d := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := (stageDarts_mem s es false hb d).1 hd
    have hmiss := kmswWalkClassBase_noMissingDarts hn c ((⟨e, hb e he⟩, false))
    refine ⟨hmiss, ?_, rfl⟩
    change s.present e = true
    change ¬ s.present e = false at hmiss
    cases h : s.present e with
    | false => exact (hmiss h).elim
    | true => rfl
  let P := simplePathOfDartChain M (kmswWalkClassBase_acyclic c) ds hds hp hchain
  have hs0 : dartTailVertex M (ds.head hds) = S := by
    apply E.injective
    apply Fin.ext
    have hh : s.west (es.head hne) = (E S).val := by
      simpa only [boundaryStart, List.head?_eq_some_head hne, Option.map_some,
        Option.some.injEq] using hS
    change stageEndpoint s (ds.head hds) = (E S).val
    simpa only [ds, stageDarts, List.head_map, List.head_attach,
      stageEndpoint, Bool.false_eq_true, ↓reduceIte] using hh
  have ht0 : dartHeadVertex M (ds.getLast hds) = T := by
    apply E.injective
    apply Fin.ext
    have hh : s.east (es.getLast hne) = (E T).val := by
      simpa only [boundaryEnd, List.getLast?_eq_getLast_of_ne_nil hne, Option.map_some,
        Option.some.injEq] using hT
    change stageEndpoint s (edgeFlip s.nextEdge (ds.getLast hds)) = (E T).val
    simpa [ds, stageDarts, stageEndpoint, edgeFlip] using hh
  refine {
    darts := P.darts
    vertices := P.vertices
    darts_length := hdlen
    vertices_length := ?_
    vertices_nodup := P.vertices_nodup
    start_vertex := P.start_vertex.trans hs0
    end_vertex := ?_
    edge_step := P.edge_step }
  · rw [P.vertices_length, hdlen]
  · have h := P.end_vertex.trans ht0
    simpa only [hdlen] using h

private theorem walkClassBoundaryData {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    let s := kmswStage (codeExtend c) (n - 1)
    let E := stageVertexEquiv (codeExtend c) (n - 1)
    let S := kmswWalkClassBaseSource c
    let T := kmswWalkClassBaseSink c
    WestEastChain s s.UL ∧ WestEastChain s s.LR ∧
    boundaryStart s s.UL = some (E S).val ∧
    boundaryEnd s s.UL = some (E T).val ∧
    boundaryStart s s.LR = some (E S).val ∧
    boundaryEnd s s.LR = some (E T).val := by
  dsimp only
  let w := codeExtend c
  let m := n - 1
  let s := kmswStage w m
  let E := stageVertexEquiv w m
  have h := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hUR, hLL,
    _, _, _, _, _⟩
  have hchain := kmswStage_boundary_chain_invariant w m
  rcases hchain with ⟨hu, hl, hs, ht, hLR, _, _⟩
  dsimp only [w, m] at hu hl hs ht hLR
  simp only [hUR, hLL, List.append_nil, List.nil_append] at hu hl hs ht
  have hUL : s.UL ≠ [] := (kmswStage_UL_nonempty_active_last w m).1
  have hS : boundaryStart s s.UL = some (E (kmswWalkClassBaseSource c)).val := by
    simp only [boundaryStart, List.head?_eq_some_head hUL, Option.map_some]
    rfl
  have hLRs : s.LR ≠ [] := hLR
  have hT : boundaryEnd s s.LR = some (E (kmswWalkClassBaseSink c)).val := by
    simp only [boundaryEnd, List.getLast?_eq_getLast_of_ne_nil hLRs, Option.map_some]
    change some (s.east (s.LR.getLast hLRs)) =
      some (stageEndpoint s ((kmswStageLRDartRun w m).head _))
    simp only [kmswStageLRDartRun, stageDarts, List.head_map, List.head_attach,
      stageEndpoint, List.head_reverse, ↓reduceIte]
    rfl
  exact ⟨hu, hl, hS, ht.trans hT, hs.symm.trans hS, hT⟩

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The UL run is a simple directed path of length `ℓ` from source to sink -/
private noncomputable def walkClassLeftPath {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    SimpleDirectedDartPath (kmswStageDirectedMap (codeExtend c) (n - 1))
      (kmswWalkClassBaseSource c) (kmswWalkClassBaseSink c) ℓ := by
  let s := kmswStage (codeExtend c) (n - 1)
  have hd := walkClassBoundaryData hn c
  exact stageSimplePath hn c s.UL
    (fun e he => stageRun_edge_bound (codeExtend c) (n - 1) e
      (Or.inl (Or.inl (Or.inl he))))
    (kmswStage_UL_nonempty_active_last (codeExtend c) (n - 1)).1 hd.1
    (kmswWalkClassBaseSource c) (kmswWalkClassBaseSink c) hd.2.2.1 hd.2.2.2.1 ℓ
    (by simpa [kmswStageULDartRun, stageDarts] using
      kmswWalkClassBase_leftDartRun_length hn c)

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The LR edges in source-to-sink order form a simple directed path of length -/
private noncomputable def walkClassRightPath {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    SimpleDirectedDartPath (kmswStageDirectedMap (codeExtend c) (n - 1))
      (kmswWalkClassBaseSource c) (kmswWalkClassBaseSink c) r := by
  let s := kmswStage (codeExtend c) (n - 1)
  have hd := walkClassBoundaryData hn c
  exact stageSimplePath hn c s.LR
    (fun e he => stageRun_edge_bound (codeExtend c) (n - 1) e (Or.inr he))
    (kmswStage_LR_nonempty (codeExtend c) (n - 1)) hd.2.1
    (kmswWalkClassBaseSource c) (kmswWalkClassBaseSink c) hd.2.2.2.2.1 hd.2.2.2.2.2 r
    (by simpa [kmswStageLRDartRun, stageDarts] using
      kmswWalkClassBase_rightDartRun_length hn c)

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The left path retains the exact UL dart run (`thm-kmsw` and -/
private theorem walkClassLeftPath_darts {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (walkClassLeftPath hn c).darts =
      kmswStageULDartRun (codeExtend c) (n - 1) := rfl

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
Reversing and opposing the right path recovers exactly the LR outer run
(`thm-kmsw` and `lem-kmsw-bdy`, -/
private theorem walkClassRightPath_outer_darts {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (walkClassRightPath hn c).darts.reverse.map
        (kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.edgeInv =
      kmswStageLRDartRun (codeExtend c) (n - 1) := by
  change (stageDarts (kmswStage (codeExtend c) (n - 1))
    (kmswStage (codeExtend c) (n - 1)).LR false
      (fun e he => stageRun_edge_bound (codeExtend c) (n - 1) e (Or.inr he))).reverse.map
      (edgeFlip (kmswStage (codeExtend c) (n - 1)).nextEdge) = _
  simp only [stageDarts, ← List.map_reverse, List.reverse_attach, List.map_map,
    kmswStageLRDartRun]
  apply List.map_congr_left
  intro e he
  apply Prod.ext
  · apply Fin.ext
    rfl
  · rfl

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The exact UL and LR boundary runs give simple directed source-to-sink
paths with the prescribed lengths (`def-kmsw`, -/
theorem kmswWalkClassBase_paths {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    ∃ P : SimpleDirectedDartPath (kmswStageDirectedMap (codeExtend c) (n - 1))
        (kmswWalkClassBaseSource c) (kmswWalkClassBaseSink c) ℓ,
    ∃ Q : SimpleDirectedDartPath (kmswStageDirectedMap (codeExtend c) (n - 1))
        (kmswWalkClassBaseSource c) (kmswWalkClassBaseSink c) r,
      P.darts = kmswStageULDartRun (codeExtend c) (n - 1) ∧
      Q.darts.reverse.map
          (kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.edgeInv =
        kmswStageLRDartRun (codeExtend c) (n - 1) := by
  exact ⟨walkClassLeftPath hn c, walkClassRightPath hn c,
    walkClassLeftPath_darts hn c, walkClassRightPath_outer_darts hn c⟩

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The final admissible KMSW stage, including the single-edge case, is a
bipolar triangulation in the general base boundary carrier (`thm-kmsw`, -/
@[expose] noncomputable def kmswWalkClassBase {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    BipolarTriangulationWithBoundaryBase
      (StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge) ℓ r := by
  let hp := kmswWalkClassBase_paths hn c
  let P := Classical.choose hp
  let Q := Classical.choose (Classical.choose_spec hp)
  have hd := Classical.choose_spec (Classical.choose_spec hp)
  have hpol := kmswWalkClassBase_poles hn c
  exact {
    map := kmswStageDirectedMap (codeExtend c) (n - 1)
    noMissingDarts := kmswWalkClassBase_noMissingDarts hn c
    planar := kmswWalkClassBase_planar c
    innerFacesDegreeThree := kmswWalkClassBase_innerFacesDegreeThree c
    acyclic := kmswWalkClassBase_acyclic c
    source := kmswWalkClassBaseSource c
    sink := kmswWalkClassBaseSink c
    isSource := hpol.1
    source_unique := hpol.2.1
    isSink := hpol.2.2.1
    sink_unique := hpol.2.2.2
    left_length_pos := kmswWalkClassBase_leftLengthPos hn c
    right_length_pos := kmswWalkClassBase_rightLengthPos hn c
    outerWord := stageOuterNonemptyWord (codeExtend c) (n - 1)
    leftPath := P
    rightPath := Q
    outerSplit := by
      rw [show P.darts = kmswStageULDartRun (codeExtend c) (n - 1) from hd.1,
        show Q.darts.reverse.map
            (kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.edgeInv =
          kmswStageLRDartRun (codeExtend c) (n - 1) from hd.2]
      exact kmswWalkClassBase_outerFourArcs hn c }

/-- Helper toward `thm-kmsw` (forward membership); not the paper result.
The base carrier retains the final KMSW stage map without modification -/
@[simp] theorem kmswWalkClassBase_map {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (kmswWalkClassBase hn c).map =
      kmswStageDirectedMap (codeExtend c) (n - 1) := rfl

end DirectedDistances.KMSW
