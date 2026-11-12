# Proposition 5.9: half-plane reflection

The separate configuration is [`palomar/principal/half-plane-reflection.json`](../palomar/principal/half-plane-reflection.json). It compares `DLQG1.Palomar.Principal.half_plane_reflection` with `DirectedDistances.Paper.Section5.prop_uihbot_sym`.

The Challenge uses the concrete stopped-excursion code law and its two-sided code map. Its geometric rooted-map carrier retains dart identity, rotation and reversal, missing-edge tags, directed tails, the ordered missing root, the outer dart, vertex positions, endpoint-preserving arc reparameterizations, face incidence and the infinite root-side orbit. The Solution proves existence and uniqueness of the Borel law before choosing it, identifies the actual source law, and transports reflection through the geometric mirror. Equality of the resulting laws uses the proved almost-everywhere zero-distance and Borel pushforward results; it does not assume equality of geometric representatives.

The Challenge selects 41 theorem targets: 23 explicit proof holes and 18 complete constructor certificates. It has no definition targets. The Solution contains no holes. The Challenge is 964 physical lines and 58,107 bytes, within the 1,000-line and 100-KiB hard limits; it exceeds the preferred 300-line advisory.

The local normal source Comparator passed with NanoDa and the Lean default kernel. A fresh axiom probe covered all 41 targets and reported only `propext`, `Classical.choice` and `Quot.sound`. The exact file hashes, target list, run metrics, kernel acceptance messages and axiom outputs are in the [portable local receipt](../verification/PALOMAR-HALF-PLANE-RESULTS.json).

These are local checks. The official workflow must still pass all ten intended configurations at one exact final commit. The eight historical official passes are bound to earlier commits. Proposition 5.16 remains pending. No Palomar intake or registration has occurred.
