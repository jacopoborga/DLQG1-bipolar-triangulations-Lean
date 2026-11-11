/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPackage

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: encode a dart by its geometric edge and
whether it agrees with the quotient representative. -/
private def boundaryChanneledDartPairEquiv
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) : D ≃ P.GeometricEdge × Bool := by
  classical
  let toPair (d : D) : P.GeometricEdge × Bool :=
    (Quotient.mk P.edgeSetoid d,
      decide (d = (Quotient.mk P.edgeSetoid d).out))
  let fromPair (q : P.GeometricEdge) (b : Bool) : D :=
    match b with
    | true => q.out
    | false => flip q.out
  refine ⟨toPair, fun x => fromPair x.1 x.2, ?_, ?_⟩
  · intro d
    dsimp [toPair, fromPair]
    by_cases h : d = (Quotient.mk P.edgeSetoid d).out
    · rw [decide_eq_true_eq.mpr h]
      exact h.symm
    · rw [decide_eq_false_iff_not.mpr h]
      have hrel : (Quotient.mk P.edgeSetoid d).out = d ∨
          (Quotient.mk P.edgeSetoid d).out = flip d := by
        exact P.geometricEdge_out_mk d
      rcases hrel with hrel | hrel
      · exact (h hrel.symm).elim
      · calc
          flip (Quotient.mk P.edgeSetoid d).out = flip (flip d) := congrArg flip hrel
          _ = d := P.flip_involutive d
  · rintro ⟨q, b⟩
    induction q using Quotient.inductionOn with
    | h d =>
      cases b <;> simp [toPair, fromPair, P.geometricEdge_flip, P.flip_ne]



































































end DirectedDistances.PaperProofs.Section3

end
end
