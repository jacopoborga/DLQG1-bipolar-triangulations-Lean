/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole8
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55RightLawClause

 

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Reader data for the actual left side of one member of the selected
whole-plane leftmost-geodesic family. Helper toward Lemma 5.5. -/
structure M0LeftSideReaderWitness (W : ℤ → Fin 3) (longest : Bool) where
  H : WholePlaneRotationHypothesis W
  h : BoundaryHitWitnesses (shiftedStream W 0)
  hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))
  hp : BoundaryHitWitnesses (kmswPastCode W)
  T : ∀ j : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h j)
  P : ∀ j : ℤ, M0CutInfiniteGeodesic W H h hLL j longest
  hleft : ∀ j, Xdp.CutLeftmostXdp W H h hp hLL longest j (P j) (T j)
  huniq : ∀ j Q, Xdp.CutLeftmostXdp W H h hp hLL longest j Q (T j) → Q = P j

/-- Helper toward Lemma 5.5: almost surely, the selected family supplies an
actual leftmost geodesic for either XDP mode at every integer index. -/
theorem ae_m0LeftSideReaderWitness :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ longest : Bool, Nonempty (M0LeftSideReaderWitness W longest) := by
  filter_upwards [ae_boundaryGluing_nonneg_right_markedIso_decodeRPlus] with W hreader
  obtain ⟨H, h, hLL, hp, hall⟩ := hreader
  intro longest
  obtain ⟨R, T, P, _hR, hleft, huniq, _hcoal, _hside⟩ := hall longest
  exact ⟨⟨H, h, hLL, hp, T, P, hleft, huniq⟩⟩

/-- Helper toward Lemma 5.5: return the class of the actual M0 left side on
the event where the selected family exists, and `none` otherwise. -/
noncomputable def m0LeftSideClassOption (longest : Bool) (k : ℤ)
    (W : ℤ → Fin 3) : Option GeometricSideClass :=
  if h : Nonempty (M0LeftSideReaderWitness W longest) then
    some (geometricSideClass
      (m0GeodesicSide (Classical.choice h).hp ((Classical.choice h).P k) .left))
  else none
































end DirectedDistances.PaperProofs.Section5
