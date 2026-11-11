/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation8

/-! Helper toward Proposition 5.16.

This module exposes the initial-direction and rotation clauses already
available for the canonical PL assembly. The topological straightening for
the transported code-map arcs remains recorded below with its exact binders. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.KMSW

/-- Helper toward Proposition 5.16. The canonical PL assembly has nonzero,
pairwise distinct initial directions at each vertex, and its stored rotation
is the counterclockwise successor of those directions. -/
theorem uibhbotD39CanonicalAssembly_initialDirectionData
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W) :
    let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
    let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
    let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
    let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
    let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    ∀ d : WholePlaneDart W,
      (G.arc d).initialDirection ≠ 0 ∧
      (∀ e : WholePlaneDart W,
        wholePlaneDartVertex W e = wholePlaneDartVertex W d →
        Complex.arg (G.arc d).initialDirection =
          Complex.arg (G.arc e).initialDirection → e = d) ∧
      CcwSuccessor
        {e | wholePlaneDartVertex W e = wholePlaneDartVertex W d}
        (fun e => (G.arc e).initialDirection) d
        (wholePlaneRotation W D.rotation d) := by
  let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  change ∀ d : WholePlaneDart W,
    (G.arc d).initialDirection ≠ 0 ∧
    (∀ e : WholePlaneDart W,
      wholePlaneDartVertex W e = wholePlaneDartVertex W d →
      Complex.arg (G.arc d).initialDirection =
        Complex.arg (G.arc e).initialDirection → e = d) ∧
    CcwSuccessor
      {e | wholePlaneDartVertex W e = wholePlaneDartVertex W d}
      (fun e => (G.arc e).initialDirection) d
      (wholePlaneRotation W D.rotation d)
  intro d
  refine ⟨G.initial_nonzero d, ?_, G.rotation_agreement d⟩
  intro e he harg
  exact (G.initial_arg_injective d e he.symm harg).symm









































































end DirectedDistances.PaperProofs.Section5

end
