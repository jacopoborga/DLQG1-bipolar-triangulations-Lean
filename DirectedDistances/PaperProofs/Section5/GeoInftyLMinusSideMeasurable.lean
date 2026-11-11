/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusSideMeasurable3
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole6

/-! # Measurability of the nonpositive left-side construction

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`),

The code-built object `lMinusDecodedSide` in
`GeoInftyNonposLeftSideWhole5` is a `GeometricSideSubmap`. Its vertices and
edges are ranges of the intrinsic natural-number maps
`lMinusCodeVertexId` and `lMinusCodeEdgeId`; its endpoints, presence,
rotation, face succession, root, boundary and seam are all fields of that
submap. Thus this contextual code-built object does carry fixed code-local
IDs. It is not yet a realization function on `LMinusSidePresentation`: its
definition also requires the whole-plane gluing witnesses and the specific
coherent hatted block. The presentation-level `hattedRealization` is only the
hatted block and cannot stand for the glued side. -/

public section
namespace DirectedDistances.PaperProofs.Section5






















end DirectedDistances.PaperProofs.Section5
