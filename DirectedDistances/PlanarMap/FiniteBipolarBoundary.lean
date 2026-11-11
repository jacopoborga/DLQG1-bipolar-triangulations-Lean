/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralBipolarBoundary

/-! # Finite bipolar maps with boundary

Combinatorial carriers toward Definition 1.9
combinatorial external face of the existing carriers, using the same
convention as the counted Section 3 anchors. These declarations do not claim
the external-face/geometric-embedding correspondence. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}





structure BipolarMapWithBoundaryBase (D : Type*) [Fintype D]
    [DecidableEq D] (ℓ r : ℕ) where
  map : DirectedMapWithMissing D
  noMissingDarts : ∀ d, ¬ map.missing d
  planar : map.toCombinatorialMap.IsPlanar
  acyclic : map.IsAcyclic
  source : MapVertex map
  sink : MapVertex map
  isSource : ¬ ∃ u, map.directedStep u source
  source_unique : ∀ v, (¬ ∃ u, map.directedStep u v) → v = source
  isSink : ¬ ∃ w, map.directedStep sink w
  sink_unique : ∀ v, (¬ ∃ w, map.directedStep v w) → v = sink
  left_length_pos : 1 ≤ ℓ
  right_length_pos : 1 ≤ r
  outerWord : NonemptyWord D
  leftPath : SimpleDirectedDartPath map source sink ℓ
  rightPath : SimpleDirectedDartPath map source sink r
  outerSplit : FourArcsWitness map outerWord leftPath.darts []
    (rightPath.darts.reverse.map map.toCombinatorialMap.edgeInv) []

namespace BipolarTriangulationWithBoundaryBase



@[expose] def toBipolarMapWithBoundaryBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    BipolarMapWithBoundaryBase D ℓ r :=
  { map := B.map
    noMissingDarts := B.noMissingDarts
    planar := B.planar
    acyclic := B.acyclic
    source := B.source
    sink := B.sink
    isSource := B.isSource
    source_unique := B.source_unique
    isSink := B.isSink
    sink_unique := B.sink_unique
    left_length_pos := B.left_length_pos
    right_length_pos := B.right_length_pos
    outerWord := B.outerWord
    leftPath := B.leftPath
    rightPath := B.rightPath
    outerSplit := B.outerSplit }

@[simp] theorem toBipolarMapWithBoundaryBase_map
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.map = B.map := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_noMissingDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.noMissingDarts = B.noMissingDarts := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_planar
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.planar = B.planar := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_acyclic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.acyclic = B.acyclic := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.source = B.source := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.sink = B.sink := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_isSource
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.isSource = B.isSource := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_source_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.source_unique = B.source_unique := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_isSink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.isSink = B.isSink := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_sink_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.sink_unique = B.sink_unique := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_left_length_pos
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.left_length_pos = B.left_length_pos := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_right_length_pos
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.right_length_pos = B.right_length_pos := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_outerWord
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.outerWord = B.outerWord := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_leftPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.leftPath = B.leftPath := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_rightPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.rightPath = B.rightPath := rfl

@[simp] theorem toBipolarMapWithBoundaryBase_outerSplit
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.toBipolarMapWithBoundaryBase.outerSplit = B.outerSplit := rfl

end BipolarTriangulationWithBoundaryBase

namespace BipolarMapWithBoundaryBase




theorem unique_source_and_sink (B : BipolarMapWithBoundaryBase D ℓ r) :
    (∃! v : MapVertex B.map, ¬ ∃ u, B.map.directedStep u v) ∧
    (∃! v : MapVertex B.map, ¬ ∃ w, B.map.directedStep v w) := by
  constructor
  · exact ⟨B.source, B.isSource, fun v hv => B.source_unique v hv⟩
  · exact ⟨B.sink, B.isSink, fun v hv => B.sink_unique v hv⟩



theorem boundary_path_lengths (B : BipolarMapWithBoundaryBase D ℓ r) :
    B.leftPath.darts.length = ℓ ∧ B.rightPath.darts.length = r := by
  exact ⟨B.leftPath.darts_length, B.rightPath.darts_length⟩

end BipolarMapWithBoundaryBase





@[expose] def IsBipolarMapWithBoundary (M : DirectedMapWithMissing D)
    (ℓ r : ℕ) : Prop :=
  ∃ B : BipolarMapWithBoundaryBase D ℓ r, B.map = M



theorem isBipolarMapWithBoundary_iff (M : DirectedMapWithMissing D)
    (ℓ r : ℕ) :
    IsBipolarMapWithBoundary M ℓ r ↔
      (1 ≤ ℓ ∧ 1 ≤ r) ∧
      M.toCombinatorialMap.IsPlanar ∧
      M.IsAcyclic ∧
      (∀ d, ¬ M.missing d) ∧
      ∃ s t : MapVertex M,
        (¬ ∃ u, M.directedStep u s) ∧
        (∀ v, (¬ ∃ u, M.directedStep u v) → v = s) ∧
        (¬ ∃ w, M.directedStep t w) ∧
        (∀ v, (¬ ∃ w, M.directedStep v w) → v = t) ∧
        ∃ W : NonemptyWord D,
        ∃ Pℓ : SimpleDirectedDartPath M s t ℓ,
        ∃ Pr : SimpleDirectedDartPath M s t r,
          FourArcsWitness M W Pℓ.darts []
            (Pr.darts.reverse.map M.toCombinatorialMap.edgeInv) [] := by
  constructor
  · rintro ⟨B, hBM⟩
    cases hBM
    exact ⟨⟨B.left_length_pos, B.right_length_pos⟩, B.planar, B.acyclic,
      B.noMissingDarts, B.source, B.sink, B.isSource, B.source_unique,
      B.isSink, B.sink_unique, B.outerWord, B.leftPath, B.rightPath,
      B.outerSplit⟩
  · rintro ⟨⟨hℓ, hr⟩, hplanar, hacyclic, hnoMissing, s, t, hs, hsu, ht,
      htu, W, Pℓ, Pr, hsplit⟩
    refine ⟨{
      map := M
      noMissingDarts := hnoMissing
      planar := hplanar
      acyclic := hacyclic
      source := s
      sink := t
      isSource := hs
      source_unique := hsu
      isSink := ht
      sink_unique := htu
      left_length_pos := hℓ
      right_length_pos := hr
      outerWord := W
      leftPath := Pℓ
      rightPath := Pr
      outerSplit := hsplit
    }, rfl⟩

end DirectedDistances.PlanarMap


