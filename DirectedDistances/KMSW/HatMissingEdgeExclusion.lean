module

public import DirectedDistances.KMSW.Beta0BoundarySuccessor
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.MhatPrimeFaceSource
import DirectedDistances.KMSW.SDPIdentifyBdy

public section
namespace DirectedDistances.KMSW

open Quiver

private theorem missingEdge_westBoundary (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (hne : ¬ EdgePresent w e) :
    ∃ k : ℤ, k ≤ -1 ∧ edgeWest w e = boundaryVertex w hb k := by
  have halloc := kmsw_edge_allocated_by_self w e
  have hfalse : (kmswStage w e).present e = false := by
    cases hp : (kmswStage w e).present e with
    | false => rfl
    | true => exact (hne ⟨e, halloc, hp⟩).elim
  have hstatus := ((kmswStage_status w e).1 e halloc).mp hfalse
  rcases hstatus with hUR | hLL
  · obtain ⟨m, hm, hpresent⟩ :=
      kmswStage_UR_edge_eventually_present_of_R_unbounded w
        hb.R_unbounded_below e e hUR
    have hallocm : e < (kmswStage w m).nextEdge :=
      halloc.trans_le (kmswStage_nextEdge_mono w hm)
    exact (hne ⟨m, hallocm, hpresent⟩).elim
  · rw [kmswStage_LL_eq] at hLL
    obtain ⟨m, hm, hem⟩ := List.mem_map.mp hLL
    have hm' := List.mem_reverse.mp hm
    have hrecord : 0 < m ∧ ∀ j < m, L w m < L w j :=
      of_decide_eq_true (List.mem_filter.mp hm').2
    let k := L w m
    have hk : k ≤ -1 := by
      have hzero : L w 0 = 0 := by simp [L]
      have hlt := hrecord.2 0 (by omega)
      dsimp [k] at hlt ⊢
      omega
    have hfind : Nat.find (hb.leftHit k hk) = m := by
      apply le_antisymm
      · exact Nat.find_min' (hb.leftHit k hk) (show L w m = k by rfl)
      · by_contra hlt
        have hvalue := Nat.find_spec (hb.leftHit k hk)
        have hstrict := hrecord.2 (Nat.find (hb.leftHit k hk)) (by omega)
        change L w (Nat.find (hb.leftHit k hk)) = k at hvalue
        dsimp [k] at hstrict hvalue
        omega
    have htime : boundaryHitTime w hb k = m := by
      unfold boundaryHitTime
      simp only [dite_eq_right (by omega : k ≠ 0),
        dite_eq_right (by omega : ¬ 0 < k)]
      exact hfind
    have heq : e = kmswLLCreatedEdge w m := by
      simpa using hem.symm
    have hleft := boundaryVertex_left_missing_edge w hb hk
    rw [htime] at hleft
    change (kmswStage w m).west (kmswLLCreatedEdge w m) =
        boundaryVertex w hb k ∧
      (kmswStage w m).east (kmswLLCreatedEdge w m) =
        boundaryVertex w hb (k + 1) ∧
      (kmswStage w m).present (kmswLLCreatedEdge w m) = false at hleft
    have hnext : 1 ≤ (kmswStage w m).nextEdge := by
      have hmono := kmswStage_nextEdge_mono w
        (m := 0) (n := m) (Nat.zero_le _)
      simpa [kmswStage, kmswInit] using hmono
    have hallocm : kmswLLCreatedEdge w m < (kmswStage w m).nextEdge := by
      simp only [kmswLLCreatedEdge]
      omega
    have hend := edge_endpoints_eq w hallocm
    refine ⟨k, hk, ?_⟩
    rw [heq]
    exact hend.1.symm.trans hleft.1

private theorem missingEdge_west_unreachable (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) (e : ℕ) (hne : ¬ EdgePresent w e) :
    ¬ MhatVertex w (edgeWest w e) := by
  obtain ⟨k, hk, hw⟩ := missingEdge_westBoundary w hb e hne
  have hne0 : edgeWest w e ≠ 0 := by
    intro hz
    have hverts : boundaryVertex w hb k = boundaryVertex w hb 0 := by
      rw [← hw, hz, boundaryVertex_zero]
    have hidx := boundaryVertex_injective w hb hverts
    omega
  have hnoIncoming (f : ℕ) (hf : EdgePresent w f) :
      edgeEast w f ≠ edgeWest w e := by
    rw [hw]
    exact boundaryVertex_nonpos_no_incoming w hb (by omega) f hf
  have noReach (v : PresentVertex w) (hv : v.id ≠ 0)
      (hi : ∀ f, EdgePresent w f → edgeEast w f ≠ v.id) :
      ¬ Reachable (⟨0⟩ : PresentVertex w) v := by
    intro ⟨p⟩
    cases p with
    | nil => exact hv rfl
    | cons p f => exact hi f.val f.property.1 f.property.2.2
  change ¬ Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e⟩
  apply noReach ⟨edgeWest w e⟩ hne0
  intro f hf
  exact hnoIncoming f hf

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result. -/
theorem mhatGeometricEdge_edgePresent (w : ℕ → Fin 3)
    (hb : BoundaryHitWitnesses w) :
    ∀ e, MhatGeometricEdge w e → EdgePresent w e := by
  intro e he
  by_contra hne
  exact missingEdge_west_unreachable w hb e hne he.1

end DirectedDistances.KMSW
