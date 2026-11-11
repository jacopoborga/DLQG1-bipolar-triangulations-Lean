module

public import DirectedDistances.PaperProofs.Section7.LongPathPrefix
import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix






@[expose] public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem infinitePresentPath_edge_injective (w : ℕ → Fin 3)
    {a : PresentVertex w} (P : InfinitePresentPath w a) :
    Function.Injective P.edge := by
  have hzero {x y : PresentVertex w} (q : Path x y) (hxy : x = y) : q.length = 0 := by
    subst y
    exact presentVertex_acyclic w _ q
  have hinitial {i j : ℕ} (hij : i < j) :
      (P.initial i).1 ≠ (P.initial j).1 := by
    intro heq
    obtain ⟨_, q, _, _, hlen, _⟩ := P.exists_shift_split i (j - i)
    have hindex : i + (j - i) = j := by omega
    have hends : (P.initial i).1 = (P.initial (i + (j - i))).1 := by
      rw [hindex]
      exact heq
    have hqzero := hzero q hends
    omega
  intro i j hij
  have hi := (P.edge_outgoing_at_initial w i).2
  have hj := (P.edge_outgoing_at_initial w j).2
  have hvertices : (P.initial i).1 = (P.initial j).1 := by
    have hid : (P.initial i).1.id = (P.initial j).1.id :=
      hi.symm.trans ((congrArg (edgeWest w) hij).trans hj)
    exact congrArg (fun k : ℕ => (⟨k⟩ : PresentVertex w)) hid
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact False.elim (hinitial hlt hvertices)
  · exact heq
  · exact False.elim (hinitial hgt hvertices.symm)



theorem first_unpresent_edge (w : ℕ → Fin 3) {a : PresentVertex w}
    (P : InfinitePresentPath w a) (n : ℕ) :
    ∃ T, ¬ (P.edge T < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge T) = true) ∧
      ∀ t, t < T → P.edge t < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge t) = true := by
  classical
  have hexit : ∃ t, ¬ (P.edge t < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present (P.edge t) = true) := by
    by_contra hnone
    have hall : ∀ t, P.edge t < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge t) = true := by
      intro t
      by_contra hbad
      exact hnone ⟨t, hbad⟩
    have hsubset : Set.range P.edge ⊆
        Set.range (fun i : Fin (kmswStage w n).nextEdge => i.val) := by
      rintro e ⟨t, rfl⟩
      exact ⟨⟨P.edge t, (hall t).1⟩, rfl⟩
    have hfinite : (Set.range P.edge).Finite :=
      (Set.finite_range fun i : Fin (kmswStage w n).nextEdge => i.val).subset hsubset
    exact (Set.infinite_range_of_injective
      (infinitePresentPath_edge_injective w P)).not_finite hfinite
  refine ⟨Nat.find hexit, Nat.find_spec hexit, ?_⟩
  intro t ht
  have hnot := Nat.find_min hexit ht
  exact Classical.not_not.mp hnot




theorem first_unpresent_edge_prefix_lifts (w : ℕ → Fin 3)
    {a : PresentVertex w} (P : InfinitePresentPath w a)
    (hP : P.HasLongestSegments) (n : ℕ) :
    ∃ T, ¬ (P.edge T < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge T) = true) ∧
      (∀ t, t < T → P.edge t < (kmswStage w n).nextEdge ∧
        (kmswStage w n).present (P.edge t) = true) ∧
      (∃ q : Path (⟨a.id⟩ : StagePresentVertex w n)
          ⟨(P.initial T).1.id⟩, q.length = (P.initial T).2.length) ∧
      (((P.initial T).2.length : WithBot ℕ) ≤
        ldpSup (⟨a.id⟩ : StagePresentVertex w n) ⟨(P.initial T).1.id⟩) := by
  cases a with
  | mk v =>
    obtain ⟨T, hExit, hBefore⟩ := first_unpresent_edge w P n
    have hp : ∀ e ∈ pathEdgeList (P.initial T).2,
        e < (kmswStage w n).nextEdge ∧ (kmswStage w n).present e = true := by
      intro e he
      rw [P.prefix_edges T] at he
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
      rw [← hi]
      exact hBefore i.val i.isLt
    obtain ⟨q, hq⟩ := path_lifts_to_stage_of_edges_present w n
      (P.initial T).2 hp
    have hbound := stage_ldp_ge_prefix_length w P hP T n hp
    exact ⟨T, hExit, hBefore, ⟨q, hq⟩, hbound⟩

end DirectedDistances.PaperProofs.Section7
