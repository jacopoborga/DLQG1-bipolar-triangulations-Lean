/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry2

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the construction's outer word contains
exactly the left path and the reversed, reversed-orientation right path.
This is a combinatorial partition, without a geometric face identification. -/
theorem boundaryChanneled_mem_outerWord_iff
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (d : Fin R.dartCount) :
    d ∈ R.B.outerWord.letters ↔
      d ∈ R.B.leftPath.darts ∨
        d ∈ R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv := by
  have h := R.B.outerSplit.2.1.mem_iff (a := d)
  simpa only [List.append_nil, List.mem_append] using h

/-- Helper toward Definition 3.2: the outer-word partition enumerates
precisely the distinguished combinatorial outer darts. -/
theorem boundaryChanneled_isOuter_iff_mem_boundaryPaths
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (d : Fin R.dartCount) :
    R.B.map.IsOuter d ↔
      d ∈ R.B.leftPath.darts ∨
        d ∈ R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv := by
  exact (mem_iff_isOuter R.B.map R.B.outerWord R.B.outerSplit.1 d).symm.trans
    (boundaryChanneled_mem_outerWord_iff R d)

/-- Helper toward Definition 3.2: finiteness identifies any two unbounded
faces of the given boundary-channeled drawing, without identifying their
border darts with the distinguished combinatorial outer face. -/
theorem boundaryChanneled_unbounded_faces_eq
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (U V : G.Face) (hU : G.IsUnbounded U) (hV : G.IsUnbounded V) : U = V := by
  obtain ⟨F, _hF, hunique⟩ := G.existsUnique_unbounded_face
  exact (hunique U hU).trans (hunique V hV).symm

































































































end DirectedDistances.PaperProofs.Section3

end
end
