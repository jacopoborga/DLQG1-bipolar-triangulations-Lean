/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart3
public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitIdentification

/-! # Simultaneous integer-time whole-plane decoding

The chronological darts are defined on the actual colimit, with proved
representative independence, injectivity and exhaustion of present darts.
The local decoder and successor identify every integer time on one common
almost-sure event. Geometric finite-ball descent and the Borel inverse remain -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory

private theorem window_active (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem transition_active (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
    window_active (shiftedStream W M) (M - N) k

/-- Helper toward Proposition 3.9: the forward dart of the actual active
edge at absolute integer time `n`, represented in a run starting no later
than `n`. Its run-independent characterization is proved next. -/
@[expose] def uibotChronologicalDart (W : ℤ → Fin 3) (n : ℤ) : WholePlaneDart W :=
  wholePlaneDartι W (-n).toNat
    (act (shiftedStream W (-n).toNat) (n + ((-n).toNat : ℤ)).toNat, false)

/-- Helper toward Proposition 3.9: every run computes the same absolute
chronological dart at each of its nonnegative stage times. -/
theorem uibotChronologicalDart_eq_run (W : ℤ → Fin 3) (N k : ℕ) :
    uibotChronologicalDart W ((k : ℤ) - N) =
      wholePlaneDartι W N (act (shiftedStream W N) k, false) := by
  apply Prod.ext
  · apply Quotient.sound
    let A := (-((k : ℤ) - N)).toNat
    refine ⟨max A N, Nat.le_max_left _ _, Nat.le_max_right _ _, ?_⟩
    change wholePlaneEdgeTrans W A (max A N) _
        (act (shiftedStream W A) ((k : ℤ) - N + (A : ℤ)).toNat) =
      wholePlaneEdgeTrans W N (max A N) _ (act (shiftedStream W N) k)
    rw [transition_active, transition_active]
    congr 1
    dsimp only [A]
    omega
  · rfl

/-- Helper toward Proposition 3.9: chronological darts never identify
different integer times, including times lying in different shifted runs. -/
theorem uibotChronologicalDart_injective (W : ℤ → Fin 3) :
    Function.Injective (uibotChronologicalDart W) := by
  intro t u he
  obtain ⟨M, ht, hu, h⟩ := Quotient.exact (congrArg Prod.fst he)
  change wholePlaneEdgeTrans W (-t).toNat M ht
      (act (shiftedStream W (-t).toNat) (t + ((-t).toNat : ℤ)).toNat) =
    wholePlaneEdgeTrans W (-u).toNat M hu
      (act (shiftedStream W (-u).toNat) (u + ((-u).toNat : ℤ)).toNat) at h
  rw [transition_active, transition_active] at h
  have hk := CutConverse.act_injective (shiftedStream W M) h
  change (-t).toNat ≤ M at ht
  change (-u).toNat ≤ M at hu
  change M - (-t).toNat + (t + ((-t).toNat : ℤ)).toNat =
    M - (-u).toNat + (u + ((-u).toNat : ℤ)).toNat at hk
  omega

/-- Helper toward Proposition 3.9: the chronological darts exhaust
exactly the forward darts of present whole-plane edges. Missing edges are
not given an orientation by this characterization. -/
theorem uibotChronologicalDart_range (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    (∃ n : ℤ, uibotChronologicalDart W n = d) ↔ wholePlaneDartTail W d := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨by change ¬ (false = true); decide, ?_⟩
    apply wholePlaneEdgePresent_ι_of_run_present
    exact ⟨_, act_lt_nextEdge _ le_rfl, kmswStage_active_present _ _⟩
  · rintro ⟨hd, hp⟩
    have hs : d.2 = false := Bool.eq_false_iff.mpr hd
    obtain ⟨⟨N, e⟩, he⟩ := Quotient.exists_rep d.1
    change wholePlaneEdgeι W N e = d.1 at he
    rw [← he, wholePlaneEdgePresent_ι] at hp
    obtain ⟨M, hNM, hM⟩ := hp
    obtain ⟨j, hj, hjp⟩ := hM M le_rfl
    obtain ⟨k, _, hk⟩ := stagePresent_exists_active (shiftedStream W M) j
      (wholePlaneEdgeTrans W N M hNM e) hj hjp
    refine ⟨(k : ℤ) - M, ?_⟩
    rw [uibotChronologicalDart_eq_run]
    apply Prod.ext
    · change wholePlaneEdgeι W M (act (shiftedStream W M) k) = d.1
      rw [← hk]
      exact (congrFun (wholePlaneEdgeι_trans W N M hNM) e).trans he
    · exact hs.symm

/-- Helper toward Proposition 3.9: the integer-time decoder reads the
literal raw-code letter, in the same whole-plane rotation at every time. -/
theorem uibotChronologicalDart_decode
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hL : ∀ N : ℕ, ∀ a : ℤ, ∃ j, L (shiftedStream W N) j ≤ a) (n : ℤ) :
    uibotLocalCodeLetter (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W) (uibotChronologicalDart W n) = W n := by
  have h := uibotLocalCodeLetter_wholePlane W H (-n).toNat
    (n + ((-n).toNat : ℤ)).toNat (hL _)
  change uibotLocalCodeLetter _ _ _ (uibotChronologicalDart W n) = _ at h
  have hi : ((n + ((-n).toNat : ℤ)).toNat : ℤ) - (-n).toNat = n := by omega
  simpa only [shiftedStream, hi] using h

/-- Helper toward Proposition 3.9: the local successor advances the same
integer-time exploration at every integer, including the transition from
negative times to the root and from the root to positive times. -/
theorem uibotChronologicalDart_next
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hp : ∀ e, wholePlaneEdgePresent W e)
    (hL : ∀ N : ℕ, ∀ a : ℤ, ∃ j, L (shiftedStream W N) j ≤ a)
    (hR : ∀ N : ℕ, ∀ a : ℤ, ∃ j, R (shiftedStream W N) j ≤ a) (n : ℤ) :
    UIBOTLocalPeanoNext (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W) (uibotChronologicalDart W n)
      (uibotChronologicalDart W (n + 1)) := by
  let N := (-n).toNat
  let j := (n + (N : ℤ)).toNat
  have he : (j : ℤ) - N = n := by dsimp only [N, j]; omega
  have he' : ((j + 1 : ℕ) : ℤ) - N = n + 1 := by omega
  rw [← he, uibotChronologicalDart_eq_run,
    show (j : ℤ) - N + 1 = ((j + 1 : ℕ) : ℤ) - N by omega,
    uibotChronologicalDart_eq_run]
  exact uibotLocalPeanoNext_wholePlane W H hp N j (hL N) (hR N)

/-- Helper toward Proposition 3.9: on the recurrent present whole-plane
carrier the local successor has a unique forward predecessor. This follows
from the proved chronological exhaustion and injectivity, without assuming
injectivity of any code-to-geometric-class map. -/
theorem uibotLocalPeanoNext_wholePlane_predecessor_unique
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hp : ∀ e, wholePlaneEdgePresent W e)
    (hL : ∀ N : ℕ, ∀ a : ℤ, ∃ j, L (shiftedStream W N) j ≤ a)
    (hR : ∀ N : ℕ, ∀ a : ℤ, ∃ j, R (shiftedStream W N) j ≤ a)
    (a b c : WholePlaneDart W) (ha : wholePlaneDartTail W a)
    (hb : wholePlaneDartTail W b)
    (hac : UIBOTLocalPeanoNext (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W) a c)
    (hbc : UIBOTLocalPeanoNext (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (wholePlaneDartTail W) b c) : a = b := by
  obtain ⟨m, rfl⟩ := (uibotChronologicalDart_range W a).2 ha
  obtain ⟨n, rfl⟩ := (uibotChronologicalDart_range W b).2 hb
  have hm := uibotLocalPeanoNext_unique _ _ _ _ _ _ hac
    (uibotChronologicalDart_next W H hp hL hR m)
  have hn := uibotLocalPeanoNext_unique _ _ _ _ _ _ hbc
    (uibotChronologicalDart_next W H hp hL hR n)
  have he := uibotChronologicalDart_injective W (hm.symm.trans hn)
  have hmn : m = n := by omega
  exact congrArg (uibotChronologicalDart W) hmn

/-- Helper toward Proposition 3.9: one almost-sure event supports literal
letter recovery and local Peano advancement simultaneously at every integer
time in the actual whole-plane colimit. No recurrence or presence hypothesis
is left on the iid statement. -/
theorem uibotChronologicalDart_ae_decode_next :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∃ H : WholePlaneRotationHypothesis W,
      ∀ n : ℤ,
        uibotLocalCodeLetter (wholePlaneRotation W H) (wholePlaneDartFlip W)
          (wholePlaneDartTail W) (uibotChronologicalDart W n) = W n ∧
        UIBOTLocalPeanoNext (wholePlaneRotation W H) (wholePlaneDartFlip W)
          (wholePlaneDartTail W) (uibotChronologicalDart W n)
          (uibotChronologicalDart W (n + 1)) := by
  filter_upwards [wholePlaneIID_ae_rotationHypothesis,
    wholePlaneIID_ae_runBoundaryDegree, wholePlaneIID_ae_uibotAllEdgesPresent]
    with W H hh hp
  have hL : ∀ N : ℕ, ∀ a : ℤ, ∃ j, L (shiftedStream W N) j ≤ a := by
    intro N a
    obtain ⟨h, _⟩ := hh N
    obtain ⟨j, hj⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨j, hj.le.trans (min_le_left _ _)⟩
  have hR : ∀ N : ℕ, ∀ a : ℤ, ∃ j, R (shiftedStream W N) j ≤ a := by
    intro N a
    obtain ⟨h, _⟩ := hh N
    exact h.R_unbounded_below a
  exact ⟨H, fun n => ⟨uibotChronologicalDart_decode W H hL n,
    uibotChronologicalDart_next W H hp hL hR n⟩⟩

private theorem left_unbounded (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (a : ℤ) : ∃ j, L w j ≤ a := by
  obtain ⟨j, hj⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
  exact ⟨j, hj.le.trans (min_le_left _ _)⟩

/-- Helper toward Proposition 3.9: a rooted isomorphism of the actual
whole-plane rotation, reversal and orientation data preserves the entire
integer-time exploration. Negative times use proved predecessor uniqueness. -/
theorem uibotChronologicalDart_equiv
    (W W' : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis W')
    (hp : ∀ e, wholePlaneEdgePresent W e)
    (hp' : ∀ e, wholePlaneEdgePresent W' e)
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N))
    (hh' : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W' N))
    (e : WholePlaneDart W ≃ WholePlaneDart W')
    (hrot : ∀ d, e (wholePlaneRotation W H d) = wholePlaneRotation W' H' (e d))
    (hflip : ∀ d, e (wholePlaneDartFlip W d) = wholePlaneDartFlip W' (e d))
    (htail : ∀ d, wholePlaneDartTail W' (e d) ↔ wholePlaneDartTail W d)
    (hroot : e (wholePlaneDartι W 0 (0, false)) = wholePlaneDartι W' 0 (0, false))
    (n : ℤ) :
    e (uibotChronologicalDart W n) = uibotChronologicalDart W' n := by
  have hL := fun N => left_unbounded _ (hh N)
  have hR := fun N => (hh N).R_unbounded_below
  have hL' := fun N => left_unbounded _ (hh' N)
  have hR' := fun N => (hh' N).R_unbounded_below
  have hnext (i : ℤ) := uibotLocalPeanoNext_equiv
    (wholePlaneRotation W H) (wholePlaneRotation W' H')
    (wholePlaneDartFlip W) (wholePlaneDartFlip W')
    (wholePlaneDartTail W) (wholePlaneDartTail W') e hrot hflip htail _ _
    (uibotChronologicalDart_next W H hp hL hR i)
  induction n using Int.induction_on with
  | zero => exact hroot
  | succ k ih =>
      have h := hnext (k : ℤ)
      rw [ih] at h
      exact uibotLocalPeanoNext_unique _ _ _ _ _ _ h
        (uibotChronologicalDart_next W' H' hp' hL' hR' (k : ℤ))
  | pred k ih =>
      have h := hnext (-(k : ℤ) - 1)
      have he : (-(k : ℤ) - 1) + 1 = -(k : ℤ) := by omega
      rw [he, ih] at h
      have h' := uibotChronologicalDart_next W' H' hp' hL' hR' (-(k : ℤ) - 1)
      rw [he] at h'
      apply uibotLocalPeanoNext_wholePlane_predecessor_unique W' H' hp' hL' hR'
        _ _ _ _ _ h h'
      · exact (htail _).2 ((uibotChronologicalDart_range W _).1 ⟨_, rfl⟩)
      · exact (uibotChronologicalDart_range W' _).1 ⟨_, rfl⟩

/-- Helper toward Proposition 3.9: the raw two-sided code is determined
by the rooted whole-plane rotation system. This is proved from the local
decoder and the integer exploration, with no assumed code-map injectivity.
Descent from geometric ball classes still requires a geometric argument. -/
theorem uibotCode_eq_of_rooted_rotation_equiv
    (W W' : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis W')
    (hp : ∀ e, wholePlaneEdgePresent W e)
    (hp' : ∀ e, wholePlaneEdgePresent W' e)
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N))
    (hh' : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W' N))
    (e : WholePlaneDart W ≃ WholePlaneDart W')
    (hrot : ∀ d, e (wholePlaneRotation W H d) = wholePlaneRotation W' H' (e d))
    (hflip : ∀ d, e (wholePlaneDartFlip W d) = wholePlaneDartFlip W' (e d))
    (htail : ∀ d, wholePlaneDartTail W' (e d) ↔ wholePlaneDartTail W d)
    (hroot : e (wholePlaneDartι W 0 (0, false)) = wholePlaneDartι W' 0 (0, false)) :
    W = W' := by
  funext n
  have h := uibotLocalCodeLetter_equiv
    (wholePlaneRotation W H) (wholePlaneRotation W' H')
    (wholePlaneDartFlip W) (wholePlaneDartFlip W')
    (wholePlaneDartTail W) (wholePlaneDartTail W') e hrot hflip htail
    (uibotChronologicalDart W n)
  rw [uibotChronologicalDart_equiv W W' H H' hp hp' hh hh' e hrot hflip htail hroot,
    uibotChronologicalDart_decode W' H' (fun N => left_unbounded _ (hh' N)),
    uibotChronologicalDart_decode W H (fun N => left_unbounded _ (hh N))] at h
  exact h.symm

private theorem chronological_finite_support
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hp : ∀ e, wholePlaneEdgePresent W e)
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N)) (n : ℤ) :
    ∃ S : Finset (WholePlaneDart W), uibotChronologicalDart W n ∈ S ∧
      ∀ (W' : ℤ → Fin 3) (H' : WholePlaneRotationHypothesis W')
        (_hp' : ∀ e, wholePlaneEdgePresent W' e)
        (_hh' : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W' N))
        (f : WholePlaneDart W → WholePlaneDart W'),
        (∀ d ∈ S,
          f (wholePlaneRotation W H d) = wholePlaneRotation W' H' (f d) ∧
          f ((wholePlaneRotation W H).symm d) = (wholePlaneRotation W' H').symm (f d) ∧
          f (wholePlaneDartFlip W d) = wholePlaneDartFlip W' (f d) ∧
          (wholePlaneDartTail W' (f d) ↔ wholePlaneDartTail W d)) →
        f (wholePlaneDartι W 0 (0, false)) = wholePlaneDartι W' 0 (0, false) →
        f (uibotChronologicalDart W n) = uibotChronologicalDart W' n := by
  classical
  have hL := fun N => left_unbounded _ (hh N)
  have hR := fun N => (hh N).R_unbounded_below
  induction n using Int.induction_on with
  | zero =>
      exact ⟨{uibotChronologicalDart W 0}, Finset.mem_singleton_self _,
        fun _ _ _ _ _ _ hroot => hroot⟩
  | succ k ih =>
      obtain ⟨S, _, hS⟩ := ih
      obtain ⟨T, _, hb, hT⟩ := uibotLocalPeanoNext_finite_support
        (wholePlaneRotation W H) (wholePlaneDartFlip W) (wholePlaneDartTail W)
        _ _ (uibotChronologicalDart_next W H hp hL hR (k : ℤ))
      refine ⟨S ∪ T, Finset.mem_union_right _ hb, ?_⟩
      intro W' H' hp' hh' f hf hroot
      have hi := hS W' H' hp' hh' f
        (fun d hd => hf d (Finset.mem_union_left _ hd)) hroot
      have hnext := hT _ (wholePlaneRotation W' H') (wholePlaneDartFlip W')
        (wholePlaneDartTail W') f
        (fun d hd => (hf d (Finset.mem_union_right _ hd)).1)
        (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.1)
        (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.2.1)
        (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.2.2)
      rw [hi] at hnext
      exact uibotLocalPeanoNext_unique _ _ _ _ _ _ hnext
        (uibotChronologicalDart_next W' H' hp'
          (fun N => left_unbounded _ (hh' N))
          (fun N => (hh' N).R_unbounded_below) (k : ℤ))
  | pred k ih =>
      obtain ⟨S, _, hS⟩ := ih
      obtain ⟨T, ha, _, hT⟩ := uibotLocalPeanoNext_finite_support
        (wholePlaneRotation W H) (wholePlaneDartFlip W) (wholePlaneDartTail W)
        _ _ (uibotChronologicalDart_next W H hp hL hR (-(k : ℤ) - 1))
      refine ⟨S ∪ T, Finset.mem_union_right _ ha, ?_⟩
      intro W' H' hp' hh' f hf hroot
      have hi := hS W' H' hp' hh' f
        (fun d hd => hf d (Finset.mem_union_left _ hd)) hroot
      have hnext := hT _ (wholePlaneRotation W' H') (wholePlaneDartFlip W')
        (wholePlaneDartTail W') f
        (fun d hd => (hf d (Finset.mem_union_right _ hd)).1)
        (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.1)
        (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.2.1)
        (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.2.2)
      have he : (-(k : ℤ) - 1) + 1 = -(k : ℤ) := by omega
      rw [he, hi] at hnext
      have hnext' := uibotChronologicalDart_next W' H' hp'
        (fun N => left_unbounded _ (hh' N))
        (fun N => (hh' N).R_unbounded_below) (-(k : ℤ) - 1)
      rw [he] at hnext'
      apply uibotLocalPeanoNext_wholePlane_predecessor_unique W' H' hp'
        (fun N => left_unbounded _ (hh' N))
        (fun N => (hh' N).R_unbounded_below) _ _ _ _ _ hnext hnext'
      · exact (hf _ (Finset.mem_union_right _ ha)).2.2.2.mpr
          ((uibotChronologicalDart_range W _).1 ⟨_, rfl⟩)
      · exact (uibotChronologicalDart_range W' _).1 ⟨_, rfl⟩

/-- Helper toward Proposition 3.9: each raw-code letter is determined
by finitely many darts of its actual rooted rotation system, uniformly
over every recurrent all-present target. Only the displayed finite
rotation, reversal and orientation data must be preserved. This finite
support has not yet been transported through geometric ball isomorphisms. -/
theorem uibotCodeLetter_finite_rotation_support
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hp : ∀ e, wholePlaneEdgePresent W e)
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N)) (n : ℤ) :
    ∃ S : Finset (WholePlaneDart W),
      ∀ (W' : ℤ → Fin 3) (H' : WholePlaneRotationHypothesis W')
        (_hp' : ∀ e, wholePlaneEdgePresent W' e)
        (_hh' : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W' N))
        (f : WholePlaneDart W → WholePlaneDart W'),
        (∀ d ∈ S,
          f (wholePlaneRotation W H d) = wholePlaneRotation W' H' (f d) ∧
          f ((wholePlaneRotation W H).symm d) = (wholePlaneRotation W' H').symm (f d) ∧
          f (wholePlaneDartFlip W d) = wholePlaneDartFlip W' (f d) ∧
          (wholePlaneDartTail W' (f d) ↔ wholePlaneDartTail W d)) →
        f (wholePlaneDartι W 0 (0, false)) = wholePlaneDartι W' 0 (0, false) →
        W n = W' n := by
  classical
  obtain ⟨S, _, hS⟩ := chronological_finite_support W H hp hh n
  obtain ⟨T, _, hT⟩ := uibotLocalCodeLetter_finite_support
    (wholePlaneRotation W H) (wholePlaneDartFlip W) (wholePlaneDartTail W)
    (uibotChronologicalDart W n)
  refine ⟨S ∪ T, ?_⟩
  intro W' H' hp' hh' f hf hroot
  have hi := hS W' H' hp' hh' f
    (fun d hd => hf d (Finset.mem_union_left _ hd)) hroot
  have h := hT _ (wholePlaneRotation W' H') (wholePlaneDartFlip W')
    (wholePlaneDartTail W') f
    (fun d hd => (hf d (Finset.mem_union_right _ hd)).1)
    (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.1)
    (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.2.1)
    (fun d hd => (hf d (Finset.mem_union_right _ hd)).2.2.2)
  rw [hi, uibotChronologicalDart_decode W' H' (fun N => left_unbounded _ (hh' N)),
    uibotChronologicalDart_decode W H (fun N => left_unbounded _ (hh N))] at h
  exact h.symm





theorem uibotCodeLetter_conull_finite_rotation_support :
    ∃ A : Set (ℤ → Fin 3), (∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∈ A) ∧
      ∀ W : ℤ → Fin 3, W ∈ A → ∃ H : WholePlaneRotationHypothesis W,
        ∀ n : ℤ, ∃ S : Finset (WholePlaneDart W),
          ∀ W' : ℤ → Fin 3, W' ∈ A →
            ∀ (H' : WholePlaneRotationHypothesis W')
              (f : WholePlaneDart W → WholePlaneDart W'),
              (∀ d ∈ S,
                f (wholePlaneRotation W H d) = wholePlaneRotation W' H' (f d) ∧
                f ((wholePlaneRotation W H).symm d) =
                  (wholePlaneRotation W' H').symm (f d) ∧
                f (wholePlaneDartFlip W d) = wholePlaneDartFlip W' (f d) ∧
                (wholePlaneDartTail W' (f d) ↔ wholePlaneDartTail W d)) →
              f (wholePlaneDartι W 0 (0, false)) = wholePlaneDartι W' 0 (0, false) →
              W n = W' n := by
  let A : Set (ℤ → Fin 3) := {W | WholePlaneRotationHypothesis W ∧
    (∀ e, wholePlaneEdgePresent W e) ∧
    ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N)}
  have hA : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∈ A := by
    filter_upwards [wholePlaneIID_ae_rotationHypothesis,
      wholePlaneIID_ae_uibotAllEdgesPresent, wholePlaneIID_ae_runBoundaryDegree]
      with W H hp hh
    exact ⟨H, hp, fun N => (hh N).choose⟩
  refine ⟨A, hA, ?_⟩
  intro W hW
  refine ⟨hW.1, ?_⟩
  intro n
  obtain ⟨S, hS⟩ := uibotCodeLetter_finite_rotation_support W hW.1 hW.2.1 hW.2.2 n
  exact ⟨S, fun W' hW' H' f hf hr => hS W' H' hW'.2.1 hW'.2.2 f hf hr⟩






























end DirectedDistances.PaperProofs.Section3

end
