module

public import DirectedDistances.KMSW.DirectedContainHat

/-! # Shifted hat vertices and limit reachability

Equivalence of the finite-stage hat set with limit reachability (R2-A24 F3),
An induced submap structure and clause 2 of that lemma are not provided. -/

public section
namespace DirectedDistances.KMSW
open Quiver

private theorem shiftNextVertexMap_unallocated (sh gl : State) (step : Step)
    (f : ℕ → ℕ) (v : ℕ)
    (hv : (kmswStepOfStep sh step).nextVertex ≤ v) :
    kmswShiftNextVertexMap sh gl step f v = f v := by
  cases step with
  | up =>
      have hne : v ≠ sh.nextVertex := by
        simp only [kmswStepOfStep, State.addEdge] at hv
        omega
      simp only [kmswShiftNextVertexMap, kmswShiftUpVertexMap, ite_eq_right hne]
  | down =>
      cases hs : sh.UR with
      | nil =>
          have hne : v ≠ sh.nextVertex := by
            simp only [kmswStepOfStep, hs, State.addEdge] at hv
            omega
          cases hg : gl.UR <;>
            simp [kmswShiftNextVertexMap, hs, hg, kmswShiftUpVertexMap,
              kmswShiftDownMismatchVertexMap, hne]
      | cons e es => simp [kmswShiftNextVertexMap, hs]
  | left =>
      cases hs : sh.UL.dropLast.reverse with
      | nil =>
          have hne : v ≠ sh.nextVertex := by
            simp only [kmswStepOfStep, hs, State.addEdge] at hv
            omega
          cases hg : gl.UL.dropLast.reverse <;>
            simp [kmswShiftNextVertexMap, hs, hg, kmswShiftUpVertexMap,
              kmswShiftLeftMismatchVertexMap, hne]
      | cons e es => simp [kmswShiftNextVertexMap, hs]

private theorem shiftVertexMap_unallocated (w : ℕ → Fin 3) (t n v : ℕ)
    (hv : (kmswStage (fun i => w (t + i)) n).nextVertex ≤ v) :
    kmswShiftVertexMapAll w t n v = kmswShiftVertexMapAll w t 0 v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hvn : (kmswStage (fun i => w (t + i)) n).nextVertex ≤ v :=
        (CutConverse.nextVertex_mono (fun i => w (t + i)) (Nat.le_succ n)).trans hv
      calc
        kmswShiftVertexMapAll w t (n + 1) v = kmswShiftVertexMapAll w t n v := by
          apply shiftNextVertexMap_unallocated
          exact hv
        _ = kmswShiftVertexMapAll w t 0 v := ih hvn

/-- Every vertex-ID map stabilizes, including on unallocated IDs -/
theorem kmswShiftVertexMapAll_stabilizes (w : ℕ → Fin 3) (t v : ℕ) :
    ∃ N, ∀ n, N ≤ n →
      kmswShiftVertexMapAll w t n v = kmswShiftVertexMapAll w t N v := by
  by_cases hv : ∃ N, v < (kmswStage (fun i => w (t + i)) N).nextVertex
  · obtain ⟨N, hN⟩ := hv
    exact ⟨N, fun n hn => kmswShiftVertexMapAll_eq_of_le w t N n v hn hN⟩
  · exact ⟨0, fun n _ => shiftVertexMap_unallocated w t n v (by
      have h := fun N hN => hv ⟨N, hN⟩
      exact Nat.le_of_not_gt (h n))⟩

/-- The vertex image of the shifted limit, given by the eventual value of the
existing compatible shift maps (`lem-directed-contain`,
unallocated isolated IDs included in `PresentVertex`; no allocation assumption
on the code is imposed. -/
@[expose] noncomputable def kmswShiftLimitVertexImage (w : ℕ → Fin 3) (t : ℕ)
    (b : PresentVertex (fun i => w (t + i))) : PresentVertex w :=
  ⟨kmswShiftVertexMapAll w t
    (Classical.choose (kmswShiftVertexMapAll_stabilizes w t b.id)) b.id⟩

/-- On an allocated vertex the limit image agrees with every finite-stage
shift embedding containing that vertex (`lem-directed-contain`, -/
theorem kmswShiftLimitVertexImage_eq_stage (w : ℕ → Fin 3) (t m : ℕ)
    (b : PresentVertex (fun i => w (t + i)))
    (hb : b.id < (kmswStage (fun i => w (t + i)) m).nextVertex) :
    kmswShiftLimitVertexImage w t b =
      (kmswShiftStageToLimit w t m).obj ⟨b.id⟩ := by
  let N := Classical.choose (kmswShiftVertexMapAll_stabilizes w t b.id)
  have hs := Classical.choose_spec (kmswShiftVertexMapAll_stabilizes w t b.id)
  apply congrArg (fun v : ℕ => (⟨v⟩ : PresentVertex w))
  calc
    kmswShiftVertexMapAll w t N b.id =
        kmswShiftVertexMapAll w t (max N m) b.id :=
      (hs (max N m) (Nat.le_max_left N m)).symm
    _ = kmswShiftVertexMapAll w t m b.id :=
      kmswShiftVertexMapAll_eq_of_le w t m (max N m) b.id
        (Nat.le_max_right N m) hb

private theorem presentPath_in_stage (u : ℕ → Fin 3)
    {a b : PresentVertex u} (p : Path a b) :
    ∃ m, Nonempty (Path (⟨a.id⟩ : StagePresentVertex u m) ⟨b.id⟩) := by
  induction p with
  | nil => exact ⟨0, ⟨Path.nil⟩⟩
  | @cons mid final p e ih =>
      obtain ⟨m, ⟨q⟩⟩ := ih
      obtain ⟨N, heN, hpN⟩ := e.property.1
      let k := max m N
      have hmk : m ≤ k := Nat.le_max_left m N
      have hNk : N ≤ k := Nat.le_max_right m N
      have hpath : Path (⟨a.id⟩ : StagePresentVertex u k) ⟨mid.id⟩ :=
        (kmswStageInclusion u m k hmk).mapPath q
      have heK := present_mono u heN hpN k hNk
      let eK : (⟨mid.id⟩ : StagePresentVertex u k) ⟶ ⟨final.id⟩ :=
        ⟨e.val, heK.1, heK.2,
          (edge_endpoints_eq u heK.1).1.trans e.property.2.1,
          (edge_endpoints_eq u heK.1).2.trans e.property.2.2⟩
      exact ⟨k, ⟨Path.cons hpath eK⟩⟩

private theorem stagePath_target_allocated (u : ℕ → Fin 3) (m : ℕ)
    {a b : StagePresentVertex u m} (p : Path a b)
    (ha : a.id < (kmswStage u m).nextVertex) :
    b.id < (kmswStage u m).nextVertex := by
  cases p with
  | nil => exact ha
  | cons q e =>
      have hb := (kmswStage_endpoints_lt_nextVertex u m e.val e.property.1).2
      rw [e.property.2.2.2] at hb
      exact hb

private theorem stageRoot_allocated (u : ℕ → Fin 3) (m : ℕ) :
    0 < (kmswStage u m).nextVertex := by
  have hm : 2 ≤ (kmswStage u m).nextVertex :=
    CutConverse.nextVertex_mono u (Nat.zero_le m)
  omega

/-- Equivalence of the finite-stage hat set with limit reachability (R2-A24 F3;
every code and every shift time, with no recurrence or boundary-hit hypothesis.
An induced submap structure and clause 2 of `lem-directed-contain` are not
provided. -/
theorem mem_kmswShiftHatVertices_iff (w : ℕ → Fin 3) (t : ℕ)
    (c : PresentVertex w) :
    c ∈ kmswShiftHatVertices w t ↔
      ∃ b : PresentVertex (fun i => w (t + i)),
        Reachable (⟨0⟩ : PresentVertex (fun i => w (t + i))) b ∧
          kmswShiftLimitVertexImage w t b = c := by
  constructor
  · rintro ⟨m, z, ⟨q⟩, hz⟩
    have hzBound := stagePath_target_allocated (fun i => w (t + i)) m q
      (stageRoot_allocated (fun i => w (t + i)) m)
    refine ⟨⟨z.id⟩, stageToLimit_reachable (fun i => w (t + i)) m ⟨q⟩, ?_⟩
    exact (kmswShiftLimitVertexImage_eq_stage w t m ⟨z.id⟩ hzBound).trans hz
  · rintro ⟨b, ⟨p⟩, hb⟩
    obtain ⟨m, ⟨q⟩⟩ := presentPath_in_stage (fun i => w (t + i)) p
    have hbBound := stagePath_target_allocated (fun i => w (t + i)) m q
      (stageRoot_allocated (fun i => w (t + i)) m)
    exact ⟨m, ⟨b.id⟩, ⟨q⟩,
      (kmswShiftLimitVertexImage_eq_stage w t m b hbBound).symm.trans hb⟩

/-- The limit vertex image is injective on allocated shifted vertices, by the
existing finite-stage simulations (`def-kmsw`, -/
theorem kmswShiftLimitVertexImage_injective_allocated (w : ℕ → Fin 3) (t : ℕ)
    {a b : PresentVertex (fun i => w (t + i))}
    (ha : ∃ m, a.id < (kmswStage (fun i => w (t + i)) m).nextVertex)
    (hb : ∃ m, b.id < (kmswStage (fun i => w (t + i)) m).nextVertex)
    (hab : kmswShiftLimitVertexImage w t a = kmswShiftLimitVertexImage w t b) :
    a = b := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  let M := max m n
  have haM : a.id < (kmswStage (fun i => w (t + i)) M).nextVertex :=
    hm.trans_le (CutConverse.nextVertex_mono (fun i => w (t + i))
      (Nat.le_max_left m n))
  have hbM : b.id < (kmswStage (fun i => w (t + i)) M).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono (fun i => w (t + i))
      (Nat.le_max_right m n))
  have hstage : (kmswShiftStageToLimit w t M).obj ⟨a.id⟩ =
      (kmswShiftStageToLimit w t M).obj ⟨b.id⟩ :=
    (kmswShiftLimitVertexImage_eq_stage w t M a haM).symm.trans
      (hab.trans (kmswShiftLimitVertexImage_eq_stage w t M b hbM))
  have hid : a.id = b.id :=
    (kmswShift_sim2_all w t M).sim.vertex_injective a.id b.id haM hbM
      (congrArg PresentVertex.id hstage)
  exact congrArg (fun v : ℕ => (⟨v⟩ : PresentVertex (fun i => w (t + i)))) hid

end DirectedDistances.KMSW
