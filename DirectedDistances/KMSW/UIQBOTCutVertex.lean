module

public import DirectedDistances.KMSW.LimitExternalFace

public section
namespace DirectedDistances.KMSW

open Filter

/- Helper for the Definition 4.2 source predicate on M-hat: vertices of its left -/
@[expose] def uiqbotLeftBoundaryVertex (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  ∃ e, limitLeftBoundaryEdge w e ∧ (edgeWest w e = v ∨ edgeEast w e = v)

/- Helper for the Definition 4.2 source predicate on M-hat: vertices of its right -/
@[expose] def uiqbotRightBoundaryVertex (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  ∃ e, limitRightBoundaryEdge w e ∧ (edgeWest w e = v ∨ edgeEast w e = v)

/- Helper Definition 4.2 source predicate on M-hat: membership in both boundary -/
@[expose] def uiqbotCutVertex (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  uiqbotLeftBoundaryVertex w v ∧ uiqbotRightBoundaryVertex w v

/- The helper Definition 4.2 source predicate on M-hat agrees with the orbit -/
theorem uiqbotCutVertex_iff_mapCutVertex (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (v : ℕ) :
    uiqbotCutVertex w v ↔ mapCutVertex w hfin v := by
  exact and_congr (mapLeftBoundaryVertex_iff_limit w hfin htrans v).symm
    (mapRightBoundaryVertex_iff_limit w hfin hL0 hR v).symm

end DirectedDistances.KMSW
