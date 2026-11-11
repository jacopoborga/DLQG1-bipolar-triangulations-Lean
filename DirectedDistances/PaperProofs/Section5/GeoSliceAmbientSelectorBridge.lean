/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination16

/-! This module records the remaining ambient bridge from the side-intrinsic
first-admissible-dart selector to `Xdp.CutLeftmostXdp`. No selector, ambient
lift, or trace comparison is asserted here. The full selector contract present
in this checkout is recorded below with its existing binders. -/

public section
namespace DirectedDistances.PaperProofs.Section5































/- Remaining sub-statements under the full binders above:

1. Coherent dart-preserving ambient lift. For an arbitrary
   `geometricSideAdjacentGeodesicCandidate` competitor, construct one
   `InfinitePresentPath` whose edge at every index is the very same side dart
   (including its geometric edge ID), and establish the ambient segment
   predicate required by `CutLeftmostXdp`. Existing finite walk lifting only
   supplies some path for each finite segment and does not preserve the chosen
   dart sequence coherently.

2. Scan-to-trace comparison. For a competitor whose earlier departure occurs
   at a shared vertex in the clockwise scan, prove that the corresponding
   ambient trace lies in the closed region between `P (k - 1)` and `T (k - 1)`.
   This requires the scan-to-departure-angle order comparison and the coherent
   lift above. The stored first-return/ordered-subsequence facts preserve dart
   encounter order but do not rule out angular wraparound at the incoming
   corner. No trace containment or leftmostness premise is supplied.

Three routes were examined before leaving this contract open (see the proved
lemmas and detailed records in `GeoSliceDetermination15.lean:691–730`):

* The induced clockwise rotation has a first-return description and an
  ordered-subsequence theorem. This stops at the missing no-wrap angle
  comparison for arbitrary finite scans.
* Ambient excursion replacement proves optimality transfer for finite paths.
  It does not construct one infinite dart-preserving lift of an arbitrary
  intrinsic candidate or its ambient segment property.
* Coalescence and face separation compare already supplied ambient rays. They
  do not produce an ambient ray from an arbitrary intrinsic competitor.

The adjacent candidate itself, its incoming scans, and the no-earlier-scan
consequence conditional on an intrinsic selector are already compiled in
`GeoSliceDetermination15.lean` and `GeoSliceDetermination16.lean`. They do not
close either sub-statement above. This helper records no paper-completion
claim. -/

end DirectedDistances.PaperProofs.Section5

