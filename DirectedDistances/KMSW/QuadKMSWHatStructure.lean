/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.HatImageLimit
public import DirectedDistances.KMSW.QuadKMSWHatFlipped

/-! # Structural source condition for the hatted KMSW limit map

This file isolates the allocation and reachability obligation used by the -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- At every stage, a left code has a predecessor in the upper-left list.
The predecessor list is `UL.dropLast.reverse`, as in `def-kmsw` -/
@[expose] def NoFreshLeftSource (u : ℕ → Fin 3) : Prop :=
  ∀ n, kmswCodeStep (u n) = .left →
    (kmswStage u n).UL.dropLast.reverse ≠ []

private theorem stage_allocated_reachable_and_incoming
    (u : ℕ → Fin 3) (hleft : NoFreshLeftSource u) :
    ∀ n,
      (∀ v, v < (kmswStage u n).nextVertex →
        Reachable (⟨0⟩ : PresentVertex u) ⟨v⟩) ∧
      (∀ v, v < (kmswStage u n).nextVertex → v ≠ 0 →
        ∃ e, e < (kmswStage u n).nextEdge ∧
          (kmswStage u n).present e = true ∧
          (kmswStage u n).east e = v ∧
          Reachable (⟨0⟩ : PresentVertex u)
            ⟨(kmswStage u n).west e⟩) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro v hv
        have hv' : v = 0 ∨ v = 1 := by
          simp [kmswStage, kmswInit] at hv
          omega
        rcases hv' with rfl | rfl
        · exact ⟨Path.nil⟩
        · have he : (⟨0⟩ : PresentVertex u) ⟶ ⟨1⟩ := by
            refine ⟨0, ⟨0, ?_, ?_⟩, ?_, ?_⟩
            · simp [kmswStage, kmswInit]
            · simp [kmswStage, kmswInit]
            · rfl
            · rfl
          exact ⟨Path.nil.cons he⟩
      · intro v hv hv0
        have hv' : v = 0 ∨ v = 1 := by
          simp [kmswStage, kmswInit] at hv
          omega
        rcases hv' with rfl | rfl
        · exact (hv0 rfl).elim
        · refine ⟨0, ?_, ?_, ?_, ?_⟩
          · simp [kmswStage, kmswInit]
          · simp [kmswStage, kmswInit]
          · simp [kmswStage, kmswInit]
          · exact ⟨Path.nil⟩
  | succ n ih =>
      obtain ⟨ihReach, ihIncoming⟩ := ih
      let s := kmswStage u n
      have hstep : kmswStage u (n + 1) = kmswStep s (u n) := by
        rfl
      have hnextMono : s.nextVertex ≤ (kmswStage u (n + 1)).nextVertex := by
        rw [hstep]
        unfold kmswStep
        cases hcode : kmswCodeStep (u n) with
        | down => cases hu : s.UR <;> simp [kmswStepOfStep, hu, State.addEdge]
        | left => cases hp : s.UL.dropLast.reverse <;>
            simp [kmswStepOfStep, hp, State.addEdge]
        | up => simp [kmswStepOfStep, State.addEdge]
      have hnextBound : (kmswStage u (n + 1)).nextVertex ≤ s.nextVertex + 1 := by
        rw [hstep]
        unfold kmswStep
        cases hcode : kmswCodeStep (u n) with
        | left =>
            cases hp : s.UL.dropLast.reverse <;>
              simp [kmswStepOfStep, hp, State.addEdge]
        | up => simp [kmswStepOfStep, State.addEdge]
        | down =>
            cases hu : s.UR <;>
              simp [kmswStepOfStep, hu, State.addEdge]
      have hReach : ∀ v, v < (kmswStage u (n + 1)).nextVertex →
          Reachable (⟨0⟩ : PresentVertex u) ⟨v⟩ := by
        intro v hv
        by_cases hvold : v < s.nextVertex
        · exact ihReach v (by simpa [s] using hvold)
        · have hvnew : v = s.nextVertex := by omega
          subst v
          cases hcode : kmswCodeStep (u n) with
          | left =>
              have hpred := hleft n hcode
              cases hp : s.UL.dropLast.reverse with
              | nil => exact (hpred hp).elim
              | cons e es =>
                  have : (kmswStage u (n + 1)).nextVertex = s.nextVertex := by
                    rw [hstep]
                    simp [kmswStep, hcode, kmswStepOfStep, hp, State.addEdge]
                  rw [this] at hv
                  omega
          | up =>
              have hsrc : s.west s.active < s.nextVertex := by
                exact (kmswStage_endpoints_lt_nextVertex u n s.active
                  (act_lt_nextEdge u (Nat.le_refl n))).1
              have hsrcReach := ihReach (s.west s.active) hsrc
              have hnew : kmswStage u (n + 1) =
                  kmswStepOfStep s .up := by
                rw [hstep, kmswStep, hcode]
              have he : (⟨s.west s.active⟩ : PresentVertex u) ⟶
                  ⟨s.nextVertex⟩ := by
                refine ⟨s.nextEdge, ⟨n + 1, ?_, ?_⟩, ?_, ?_⟩
                · rw [hnew]
                  simp [kmswStepOfStep, State.addEdge]
                · rw [hnew]
                  simp [kmswStepOfStep, State.addEdge]
                · calc
                    edgeWest u s.nextEdge =
                        (kmswStage u (n + 1)).west s.nextEdge :=
                      (edge_endpoints_eq u (by
                        rw [hnew]
                        simp [kmswStepOfStep, State.addEdge])).1.symm
                    _ = s.west s.active := by
                      rw [hnew]
                      simp [kmswStepOfStep, State.addEdge]
                · calc
                    edgeEast u s.nextEdge =
                        (kmswStage u (n + 1)).east s.nextEdge :=
                      (edge_endpoints_eq u (by
                        rw [hnew]
                        simp [kmswStepOfStep, State.addEdge])).2.symm
                    _ = s.nextVertex := by
                      rw [hnew]
                      simp [kmswStepOfStep, State.addEdge]
              obtain ⟨p⟩ := hsrcReach
              exact ⟨p.cons he⟩
          | down =>
              cases hu : s.UR with
              | cons e es =>
                  have : (kmswStage u (n + 1)).nextVertex = s.nextVertex := by
                    rw [hstep]
                    simp [kmswStep, hcode, kmswStepOfStep, hu]
                  rw [this] at hv
                  omega
              | nil =>
                  have hsrc : s.east s.active < s.nextVertex := by
                    exact (kmswStage_endpoints_lt_nextVertex u n s.active
                      (act_lt_nextEdge u (Nat.le_refl n))).2
                  have hsrcReach := ihReach (s.east s.active) hsrc
                  have hnew : kmswStage u (n + 1) =
                      kmswStepOfStep s .down := by
                    rw [hstep, kmswStep, hcode]
                  have he : (⟨s.east s.active⟩ : PresentVertex u) ⟶
                      ⟨s.nextVertex⟩ := by
                    refine ⟨s.nextEdge, ⟨n + 1, ?_, ?_⟩, ?_, ?_⟩
                    · rw [hnew]
                      simp [kmswStepOfStep, hu, State.addEdge]
                    · rw [hnew]
                      simp [kmswStepOfStep, hu, State.addEdge]
                    · calc
                        edgeWest u s.nextEdge =
                            (kmswStage u (n + 1)).west s.nextEdge :=
                          (edge_endpoints_eq u (by
                            rw [hnew]
                            simp [kmswStepOfStep, hu, State.addEdge])).1.symm
                        _ = s.east s.active := by
                          rw [hnew]
                          simp [kmswStepOfStep, hu, State.addEdge]
                    · calc
                        edgeEast u s.nextEdge =
                            (kmswStage u (n + 1)).east s.nextEdge :=
                          (edge_endpoints_eq u (by
                            rw [hnew]
                            simp [kmswStepOfStep, hu, State.addEdge])).2.symm
                        _ = s.nextVertex := by
                          rw [hnew]
                          simp [kmswStepOfStep, hu, State.addEdge]
                  obtain ⟨p⟩ := hsrcReach
                  exact ⟨p.cons he⟩
      have hIncoming : ∀ v, v < (kmswStage u (n + 1)).nextVertex → v ≠ 0 →
          ∃ e, e < (kmswStage u (n + 1)).nextEdge ∧
            (kmswStage u (n + 1)).present e = true ∧
            (kmswStage u (n + 1)).east e = v ∧
            Reachable (⟨0⟩ : PresentVertex u)
              ⟨(kmswStage u (n + 1)).west e⟩ := by
        intro v hv hv0
        by_cases hvold : v < s.nextVertex
        · obtain ⟨e, he, hp, heast, hwest⟩ := ihIncoming v
            (by simpa [s] using hvold) hv0
          have he' : e < s.nextEdge := by simpa [s] using he
          refine ⟨e, ?_, ?_, ?_, ?_⟩
          · rw [hstep]
            exact he'.trans_le (by
              unfold kmswStep
              cases hcode : kmswCodeStep (u n) with
              | left => cases hpred : s.UL.dropLast.reverse <;>
                  simp [kmswStepOfStep, hpred, State.addEdge] <;> omega
              | up => simp [kmswStepOfStep, State.addEdge] <;> omega
              | down => cases hu : s.UR <;>
                  simp [kmswStepOfStep, hu, State.addEdge] <;> omega)
          · rw [hstep]
            have hp' : (kmswStep s (u n)).present e = true := by
              rw [kmswStep_present_existing s (u n) he']
              have hpOld : s.present e = true := by simpa [s] using hp
              simp [hpOld]
            exact hp'
          · have hend := kmswStage_endpoints_stable u (Nat.le_succ n) he
            simpa [s] using hend.2.trans heast
          · have hend := kmswStage_endpoints_stable u (Nat.le_succ n) he
            have hwEq : (kmswStage u (n + 1)).west e = s.west e := by
              simpa [s] using hend.1
            rw [hwEq]
            exact hwest
        · have hvnew : v = s.nextVertex := by omega
          subst v
          cases hcode : kmswCodeStep (u n) with
          | left =>
              have hpred := hleft n hcode
              cases hp : s.UL.dropLast.reverse with
              | nil => exact (hpred hp).elim
              | cons e es =>
                  have : (kmswStage u (n + 1)).nextVertex = s.nextVertex := by
                    rw [hstep]
                    simp [kmswStep, hcode, kmswStepOfStep, hp, State.addEdge]
                  rw [this] at hv
                  omega
          | up =>
              have hnew : kmswStage u (n + 1) = kmswStepOfStep s .up := by
                rw [hstep, kmswStep, hcode]
              refine ⟨s.nextEdge, ?_, ?_, ?_, ?_⟩
              · rw [hnew]
                simp [kmswStepOfStep, State.addEdge]
              · rw [hnew]
                simp [kmswStepOfStep, State.addEdge]
              · rw [hnew]
                simp [kmswStepOfStep, State.addEdge]
              · have hsrc : s.west s.active < s.nextVertex := by
                  exact (kmswStage_endpoints_lt_nextVertex u n s.active
                    (act_lt_nextEdge u (Nat.le_refl n))).1
                have hsrcReach := hReach (s.west s.active)
                  (hsrc.trans_le hnextMono)
                simpa [hnew, kmswStepOfStep, State.addEdge] using hsrcReach
          | down =>
              cases hu : s.UR with
              | cons e es =>
                  have : (kmswStage u (n + 1)).nextVertex = s.nextVertex := by
                    rw [hstep]
                    simp [kmswStep, hcode, kmswStepOfStep, hu]
                  rw [this] at hv
                  omega
              | nil =>
                  have hnew : kmswStage u (n + 1) = kmswStepOfStep s .down := by
                    rw [hstep, kmswStep, hcode]
                  refine ⟨s.nextEdge, ?_, ?_, ?_, ?_⟩
                  · rw [hnew]
                    simp [kmswStepOfStep, hu, State.addEdge]
                  · rw [hnew]
                    simp [kmswStepOfStep, hu, State.addEdge]
                  · rw [hnew]
                    simp [kmswStepOfStep, hu, State.addEdge]
                  · have hsrc : s.east s.active < s.nextVertex := by
                      exact (kmswStage_endpoints_lt_nextVertex u n s.active
                        (act_lt_nextEdge u (Nat.le_refl n))).2
                    have hsrcReach := hReach (s.east s.active)
                      (hsrc.trans_le hnextMono)
                    simpa [hnew, kmswStepOfStep, hu, State.addEdge] using hsrcReach
      exact ⟨hReach, hIncoming⟩

/-- Under `NoFreshLeftSource`, every allocated non-root vertex is the east
endpoint of a present edge whose west endpoint is root-reachable. The east
endpoint is itself root-reachable. This is a structural helper for -/
theorem allocated_nonroot_east_reachable_of_noFreshLeftSource
    (u : ℕ → Fin 3) (hleft : NoFreshLeftSource u)
    (a : PresentVertex u)
    (ha : ∃ m, a.id < (kmswStage u m).nextVertex)
    (ha0 : a.id ≠ 0) :
    ∃ e, EdgePresent u e ∧ edgeEast u e = a.id ∧
      Reachable (⟨0⟩ : PresentVertex u) ⟨edgeWest u e⟩ ∧
      Reachable (⟨0⟩ : PresentVertex u) a := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨_, hin⟩ := stage_allocated_reachable_and_incoming u hleft m
  obtain ⟨e, he, hp, heast, hwest⟩ := hin a.id hm ha0
  have hePresent : EdgePresent u e := ⟨m, he, hp⟩
  have hEnds := edge_endpoints_eq u he
  refine ⟨e, hePresent, ?_, ?_, ?_⟩
  · exact hEnds.2.symm.trans heast
  · simpa [hEnds.1] using hwest
  · simpa [heast] using
      (stage_allocated_reachable_and_incoming u hleft m).1 a.id hm

/-- The structural hypothesis implies the local field required by
`HatImageLimitInput`, with the stronger east-endpoint orientation -/
theorem allocated_nonroot_incident_of_noFreshLeftSource
    (u : ℕ → Fin 3) (hleft : NoFreshLeftSource u) :
    ∀ a : PresentVertex u,
      (∃ m, a.id < (kmswStage u m).nextVertex) → a.id ≠ 0 →
      ∃ e, EdgePresent u e ∧
        (edgeWest u e = a.id ∨ edgeEast u e = a.id) ∧
        Reachable (⟨0⟩ : PresentVertex u) ⟨edgeWest u e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex u) ⟨edgeEast u e⟩ := by
  intro a ha ha0
  obtain ⟨e, he, heast, hw, ht⟩ :=
    allocated_nonroot_east_reachable_of_noFreshLeftSource u hleft a ha ha0
  refine ⟨e, he, Or.inr heast, hw, ?_⟩
  simpa only [heast] using ht

end DirectedDistances.KMSW
