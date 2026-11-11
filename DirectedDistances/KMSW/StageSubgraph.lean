module

public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.DirectedPath.Distance
public import DirectedDistances.DirectedPath.Finite
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Supporting lemmas for paper labels `def-ldp` (see CORRESPONDENCE.md). -/








@[expose] public section
namespace DirectedDistances.KMSW

open Quiver

/-- A vertex ID in the present-edge graph of stage `n` of the KMSW construction -/
structure StagePresentVertex (w : ℕ → Fin 3) (n : ℕ) where
  id : ℕ
  deriving DecidableEq

/-- One arrow for each edge ID allocated and present at stage `n`, with that
stage's endpoints, mirroring `presentVertexQuiver` for the limit -/
instance stagePresentQuiver (w : ℕ → Fin 3) (n : ℕ) :
    Quiver (StagePresentVertex w n) where
  Hom u v := {e : ℕ // e < (kmswStage w n).nextEdge ∧
    (kmswStage w n).present e = true ∧
    (kmswStage w n).west e = u.id ∧ (kmswStage w n).east e = v.id}

/-- Presence is permanent along the stages: an allocated present edge at stage `n`
is allocated and present at every later stage (`remark-kmsw-infinite`, -/
theorem present_mono (w : ℕ → Fin 3) {n e : ℕ}
    (he : e < (kmswStage w n).nextEdge) (hp : (kmswStage w n).present e = true) :
    ∀ m, n ≤ m → e < (kmswStage w m).nextEdge ∧ (kmswStage w m).present e = true := by
  intro m hm
  refine ⟨he.trans_le (kmswStage_nextEdge_mono w hm), ?_⟩
  induction m, hm using Nat.le_induction with
  | base => exact hp
  | succ m hm ih =>
    change (kmswStep (kmswStage w m) (w m)).present e = true
    rw [kmswStep_present_existing _ _ (he.trans_le (kmswStage_nextEdge_mono w hm))]
    split
    · rfl
    · exact ih

/-- A present edge at stage `n` is present in the limit -/
theorem EdgePresent.of_stage_present {w : ℕ → Fin 3} {n e : ℕ}
    (he : e < (kmswStage w n).nextEdge) (hp : (kmswStage w n).present e = true) :
    EdgePresent w e :=
  ⟨n, he, hp⟩

/-- Endpoints of an edge present at stage `n` are the same at every later stage -/
theorem present_endpoints_stable (w : ℕ → Fin 3) {n e : ℕ}
    (he : e < (kmswStage w n).nextEdge) (hp : (kmswStage w n).present e = true)
    {m : ℕ} (hm : n ≤ m) :
    (kmswStage w m).west e = (kmswStage w n).west e ∧
      (kmswStage w m).east e = (kmswStage w n).east e := by
  have h1 := edge_endpoints_eq w he
  have h2 := edge_endpoints_eq w (present_mono w he hp m hm).1
  exact ⟨h2.1.trans h1.1.symm, h2.2.trans h1.2.symm⟩



def stageToLimit (w : ℕ → Fin 3) (n : ℕ) :
    Prefunctor (StagePresentVertex w n) (PresentVertex w) where
  obj v := ⟨v.id⟩
  map {_ _} e :=
    ⟨e.val, ⟨n, e.property.1, e.property.2.1⟩,
      (edge_endpoints_eq w e.property.1).1.symm.trans e.property.2.2.1,
      (edge_endpoints_eq w e.property.1).2.symm.trans e.property.2.2.2⟩

 
theorem stageToLimit_length (w : ℕ → Fin 3) (n : ℕ) {a b : StagePresentVertex w n}
    (p : Path a b) : ((stageToLimit w n).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]



theorem stageToLimit_reachable (w : ℕ → Fin 3) (n : ℕ) {a b : StagePresentVertex w n}
    (h : Reachable a b) :
    Reachable (⟨a.id⟩ : PresentVertex w) ⟨b.id⟩ := by
  obtain ⟨p⟩ := h
  exact ⟨(stageToLimit w n).mapPath p⟩



theorem sdp_limit_le_sdp_stage (w : ℕ → Fin 3) (n : ℕ) (a b : StagePresentVertex w n) :
    sdp (⟨a.id⟩ : PresentVertex w) ⟨b.id⟩ ≤ sdp a b := by
  show _ ≤ ⨅ p : Path a b, (p.length : ℕ∞)
  refine le_iInf fun p => ?_
  calc sdp (⟨a.id⟩ : PresentVertex w) ⟨b.id⟩
      ≤ (((stageToLimit w n).mapPath p).length : ℕ∞) := sdp_le_length _
    _ = p.length := by rw [stageToLimit_length]



theorem pathLengths_stage_subset (w : ℕ → Fin 3) (n : ℕ) (a b : StagePresentVertex w n) :
    pathLengths a b ⊆ pathLengths (⟨a.id⟩ : PresentVertex w) ⟨b.id⟩ := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(stageToLimit w n).mapPath p, stageToLimit_length w n p⟩

/-- Longest-path supremum with `⊥` for unreachable, on the stage quiver: the
body of `finiteLdp` without a `Fintype` hypothesis (`def-ldp`). -/
noncomputable def ldpSup {V : Type*} [Quiver V] (a b : V) : WithBot ℕ :=
  sSup ((fun n : ℕ => (n : WithBot ℕ)) '' pathLengths a b)

/-- Unreachable pairs have `⊥` longest-path supremum, never `0`. -/
theorem ldpSup_eq_bot_of_not_reachable {V : Type*} [Quiver V] {a b : V}
    (h : ¬ Reachable a b) : ldpSup a b = ⊥ := by
  have he : pathLengths a b = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨p, rfl⟩
    exact h ⟨p⟩
  simp only [ldpSup, he, Set.image_empty, csSup_empty]



theorem ldpSup_stage_le_ldpSup_limit (w : ℕ → Fin 3) (n : ℕ)
    (a b : StagePresentVertex w n)
    (hb : BddAbove (pathLengths (⟨a.id⟩ : PresentVertex w) ⟨b.id⟩)) :
    ldpSup a b ≤ ldpSup (⟨a.id⟩ : PresentVertex w) ⟨b.id⟩ := by
  by_cases hr : Reachable a b
  · obtain ⟨p⟩ := hr
    apply csSup_le_csSup
    · obtain ⟨N, hN⟩ := hb
      refine ⟨(N : WithBot ℕ), ?_⟩
      rintro _ ⟨m, hm, rfl⟩
      exact WithBot.coe_le_coe.mpr (hN hm)
    · exact ⟨p.length, ⟨p.length, ⟨p, rfl⟩, rfl⟩⟩
    · exact Set.image_mono (pathLengths_stage_subset w n a b)
  · rw [ldpSup_eq_bot_of_not_reachable hr]
    exact bot_le

/-- The initial edge `λ_0 = act w 0` is present at every stage -/
theorem initial_edge_present (w : ℕ → Fin 3) (n : ℕ) :
    0 < (kmswStage w n).nextEdge ∧ (kmswStage w n).present 0 = true :=
  present_mono w (n := 0) Nat.one_pos rfl n (Nat.zero_le n)



theorem initial_edge_endpoints (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).west 0 = 0 ∧ (kmswStage w n).east 0 = 1 :=
  present_endpoints_stable w (n := 0) Nat.one_pos rfl (Nat.zero_le n)



def initialEdgeArrow (w : ℕ → Fin 3) (n : ℕ) :
    (⟨0⟩ : StagePresentVertex w n) ⟶ ⟨1⟩ :=
  ⟨0, (initial_edge_present w n).1, (initial_edge_present w n).2,
    (initial_edge_endpoints w n).1, (initial_edge_endpoints w n).2⟩



theorem sdp_stage_x0_x1 (w : ℕ → Fin 3) (n : ℕ) :
    sdp (⟨0⟩ : StagePresentVertex w n) ⟨1⟩ = 1 := by
  apply le_antisymm
  · simpa using sdp_le_length (Hom.toPath (initialEdgeArrow w n))
  · rw [Order.one_le_iff_ne_zero, Ne, sdp_eq_zero_iff]
    intro h
    exact Nat.zero_ne_one (congrArg StagePresentVertex.id h)

end DirectedDistances.KMSW
