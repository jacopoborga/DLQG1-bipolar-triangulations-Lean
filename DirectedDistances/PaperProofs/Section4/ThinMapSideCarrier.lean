module

public import DirectedDistances.KMSW.InfiniteRotation
public import DirectedDistances.KMSW.InfiniteGeodesic
public import Mathlib.Logic.Relation

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/

























public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW




inductive ThinMapSide where
  | left
  | right

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)












structure ThinMapBoundaryRays where
  left : ℕ → ℕ × Bool
  right : ℕ → ℕ × Bool
  left_step : ∀ n, kmswInfFaceSucc w hfin (left n) = left (n + 1)
  right_step : ∀ n, kmswInfFaceSucc w hfin (right (n + 1)) = right n
  junction : kmswInfFaceSucc w hfin (right 0) = left 0
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  rays_disjoint : Disjoint (Set.range left) (Set.range right)

variable (P : InfinitePresentPath w ⟨0⟩) (B : ThinMapBoundaryRays w hfin)




@[expose] def thinMapBoundaryArc (side : ThinMapSide) : Set (ℕ × Bool) :=
  match side with
  | .left => Set.range B.left
  | .right => Set.range B.right




@[expose] def thinMapSeamDarts : Set (ℕ × Bool) :=
  {d | ∃ n, P.edge n = d.1}





@[expose] def thinMapSideSeeds (side : ThinMapSide) : Set (ℕ × Bool) :=
  thinMapBoundaryArc w hfin B side ∪
    {d | ∃ n, d = (P.edge n, match side with | .left => false | .right => true)}





@[expose] def thinMapSideStep (side : ThinMapSide) (d e : ℕ × Bool) : Prop :=
  (e = kmswInfFaceSucc w hfin d ∧
    (d ∉ Set.range B.left ∪ Set.range B.right ∨
      (d ∈ thinMapBoundaryArc w hfin B side ∧
        e ∈ thinMapBoundaryArc w hfin B side))) ∨
  (e = (d.1, !d.2) ∧ d ∉ thinMapSeamDarts w P)





@[expose] def thinMapSideClosure (side : ThinMapSide) : Set (ℕ × Bool) :=
  {d | ∃ a ∈ thinMapSideSeeds w hfin P B side,
    Relation.ReflTransGen (thinMapSideStep w hfin P B side) a d}





@[expose] def thinMapSideDarts (side : ThinMapSide) : Set (ℕ × Bool) :=
  thinMapSideClosure w hfin P B side ∪ thinMapSeamDarts w P





theorem thinMapSide_seam_mem (side : ThinMapSide) (n : ℕ) (b : Bool) :
    (P.edge n, b) ∈ thinMapSideDarts w hfin P B side := by
  exact Or.inr ⟨n, rfl⟩





theorem thinMapSide_edgeInv_mem (side : ThinMapSide) {d : ℕ × Bool}
    (hd : d ∈ thinMapSideDarts w hfin P B side) :
    (d.1, !d.2) ∈ thinMapSideDarts w hfin P B side := by
  rcases hd with hclosure | hseam
  · by_cases hseam : d ∈ thinMapSeamDarts w P
    · exact Or.inr hseam
    · rcases hclosure with ⟨a, ha, hreach⟩
      exact Or.inl ⟨a, ha, Relation.ReflTransGen.tail hreach (Or.inr ⟨rfl, hseam⟩)⟩
  · exact Or.inr hseam

end DirectedDistances.PaperProofs.Section4
