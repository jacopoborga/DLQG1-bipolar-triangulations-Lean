# DLQG1: bipolar triangulations in Lean

[![Lean verification](https://github.com/jacopoborga/DLQG1-bipolar-triangulations-Lean/actions/workflows/lean.yml/badge.svg)](https://github.com/jacopoborga/DLQG1-bipolar-triangulations-Lean/actions/workflows/lean.yml)
[![Comparator official preflight](https://github.com/jacopoborga/DLQG1-bipolar-triangulations-Lean/actions/workflows/comparator.yml/badge.svg)](https://github.com/jacopoborga/DLQG1-bipolar-triangulations-Lean/actions/workflows/comparator.yml)

Both workflows are manual-dispatch preparation checks. The Appendix configuration has an official PASS at the exact commit recorded below; newly integrated configurations require their own official runs.

A Lean 4 / Mathlib development of **90 numbered definitions, theorems, propositions and lemmas**, including Appendix A, associated with *Directed distances in bipolar-oriented triangulations: exact exponents and scaling limits* by **Jacopo Borga and Ewain Gwynne** ([arXiv:2510.26123](https://arxiv.org/abs/2510.26123)).

**Author-approved public release.** The accepted 90-item statements are preserved. The correspondence table uses the current author-supplied manuscript. Additional source-domain views and supporting proofs account for its revised boundary conventions; the general implementation interfaces remain available. The precise rendering conventions are recorded below.

## What is included

The library contains the 90 entries, their defining interfaces and proof dependencies: directed distances and geodesics, KMSW constructions and rooted plane-map limits, Busemann functions and stable limits, finite-cell estimates, and the Appendix Tauberian arguments. Required supporting lemmas are included. Supplementary developments and manuscript PDFs, LaTeX files and source archives are excluded.

- [CORRESPONDENCE.md](CORRESPONDENCE.md) maps every current paper label and number to its exact Lean export.
- [ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md) records scope conventions and source-alignment issues.
- [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) identifies the exact public files and their hashes.
- [PUBLICATION.md](PUBLICATION.md) records author approval and preservation of historical receipts.
- [VERIFICATION.md](VERIFICATION.md) records the isolated build, integrity checks, axiom audit and fresh kernel replay.

The main entry point is `import DirectedDistances`. It reexports `DirectedDistances.DeliveryVerificationRoot`; the source-facing statements are organized under `DirectedDistances/Paper/Section1`, `Section3`, …, `Section7` and `AppendixA`. The full statements and definitions are in the files linked from the correspondence table.

## Scope and faithfulness

The corrected numbering is **Definition 3.8** for local topology, **Proposition 3.9** for the whole-plane KMSW limit, and **Lemma 3.10** for the infinite-map boundary statement. Public Lean declaration names remain stable. Implementation identifiers such as `D39` retain the original numbering; the correspondence table is authoritative for this manuscript revision.

The formalization preserves plane orientation, rotations, incidence, geometric missing edges and the ordered root. Unreachable longest- and shortest-path distances are negative and positive infinity respectively. Simultaneous probability-one statements, equality in law and functional convergence are distinguished.

Definition 3.17 is represented by a source-facing view that combines the general boundary-channeled predicate with simple boundary or the single-edge exception. The supporting proofs identify the right-boundary-one classes and the finite sampling laws used downstream. Definition 1.1’s external-boundary convention has a separate source-domain predicate, with proofs for the finite KMSW maps, the UIQBOT on its existing probability-one event, and the whole-plane limit. These views are in [SourceBoundaryChanneled.lean](verification/SourceBoundaryChanneled.lean), [SourceBoundaryDomain.lean](verification/SourceBoundaryDomain.lean) and [SourceScopeCheck.lean](verification/SourceScopeCheck.lean). They do not identify the broader generic classes with the restricted source classes. Other recorded conventions include extended-supremum longest-path distance, left-limit negative-time reversal, the marked vertex in Lemma 3.12 and the boundary-channeled future in Lemma 5.10.

## Errata and deviations

There are **17 numbered entries with explicit rendering or scope notes**, including **four approved conventions still unprinted in the manuscript**. The [deviations record](docs/ERRATA-AND-DEVIATIONS.md) gives counts by source section and distinguishes proved source-domain bindings from previously approved conventions that are not yet literal in the supplied text. These notes are part of the correspondence claim.

## Building and verification

The pinned toolchain is **Lean `v4.36.0-rc2`**. Mathlib is pinned to **`9d581dfff2e41de989072ea63abf3daf69311520`**; `lake-manifest.json` fixes all dependency revisions. Install [elan](https://github.com/leanprover/elan), then from the repository root run:

```bash
LEAN_NUM_THREADS=4 bash scripts/verify.sh
```

The script builds pinned dependencies when their compiled cache is unavailable. A verified pinned dependency cache can be reused without changing the manifest. The scripts use Bash and Python’s standard library (Python 3.6 or newer); validation was performed on Linux. `LEAN_NUM_THREADS=4 bash scripts/verify.sh` runs the same checks and stores local logs below `.lake/release-verification/`. When reusing an already verified, metadata-free dependency cache, the supported Lake package override can be supplied as `DLQG_LAKE_PACKAGES=.lake/offline-packages.json scripts/verify.sh`; it does not change the pinned project configuration.

The axiom probes list every advertised wrapper and the required implementation exports. The expected foundational axioms are `propext`, `Classical.choice` and `Quot.sound`. The fresh replay checks the compiled proof terms; correspondence review separately addresses their mathematical interpretation.

## Palomar preparation

This preparation keeps the complete 90-entry correspondence separate from
optional Comparator selections. The natural-valued Appendix A.2 pilot
(`palomar/comparator-pilot.json`,
`DLQG1.Palomar.tauberian_below_one`) passed sandboxed Comparator, NanoDa and
Lean kernel checks, with no blocker from a separate source-fidelity review.
The root `comparator.json` selects the six numbered Appendix lemmas under
`DLQG1.Palomar.AppendixA`; it separately passed local sandboxed Comparator, NanoDa and Lean checks.
A separate source-fidelity review found no blocker for all six statements.

The seven introductory theorems, including Theorem 1.13, and Propositions 5.9
and 5.16 have a [planned principal-entry map](docs/PALOMAR-PREPARATION.md).
The finite configurations for [Theorem 1.11](docs/PALOMAR-BOLTZMANN-DISTANCES.md),
[Theorem 1.12](docs/PALOMAR-CELLLDP.md) and
[Theorem 1.13](docs/PALOMAR-CELLSDP.md) pass normal local Comparator,
NanoDa, default Lean and axiom checks, with independent fidelity review.
[Theorem 1.4](docs/PALOMAR-BUSEMANN.md) also passes normal source Comparator,
Lean/NanoDa and its complete construction/axiom audits. Five other principal
configurations remain in preparation.
No configuration claims that all 90 entries have been compared or registered.

Run `bash scripts/verify-palomar.sh` to reproduce the pilot, Appendix, Busemann and three finite principal configurations,
Challenge-hole controls and their exact Solution axiom audits. The generated
logs are below `.lake/palomar-evidence/verify-<UTC>-<pid>/`; the portable
[comparison receipts](verification/PALOMAR-RESULTS.json) record the checked scope.

The [preparation record](docs/PALOMAR-PREPARATION.md) pins the policy, metadata
schema and official verification pipeline, explains each selection and lists
the remaining definition obligations. The two workflow badges above are draft
manual checks: Lean source/axiom/kernel verification and the official reusable
Comparator preflight. The six-Appendix configuration passed the complete
[official full preflight](https://github.com/jacopoborga/DLQG1-bipolar-triangulations-Lean/actions/runs/43154846070)
at commit `e2e3be75d8e7b39eaf0d8ce24b504287421c4a41`.
[Portable official receipts](verification/PALOMAR-OFFICIAL-RESULTS.json) identify
that exact checked commit and configuration. Subsequent commits require their
own successful official runs; an earlier PASS does not certify later changes.
Preparation and mechanical checks do not perform Palomar intake, editorial
review or registration.

## How this was built

AI coding agents produced the Lean development under **Jacopo Borga’s supervision**. Human decisions covered mathematical interpretation and corrections; Lean checked the formal proof terms. Separate agent reviews examined source correspondence and release integrity. This is distinct from external human peer review.

Development used OpenAI Codex models in the Sol, Luna and Astra families and Anthropic Claude models. The v0.1.0 public-release preparation and independent reviews used Sol. The Palomar preparation uses Sol and Luna agents, with no new Astra work. Tools, review scope and the limits of available cost information are recorded in [formalization.yaml](formalization.yaml). Total subscription and infrastructure spending was not separately tracked for this export.

## Credits and citation

The mathematical paper is by **Jacopo Borga and Ewain Gwynne**. The formalization was directed by **Jacopo Borga**. The project builds on Lean 4, Mathlib, Lake and elan. The release checklist and documentation structure follow Scott Armstrong’s `lean-public-release` workflow and [HighContrastHomogenization](https://github.com/scottnarmstrong/HighContrastHomogenization).

Please cite the software using [CITATION.cff](CITATION.cff), together with the paper. Paper authorship and formalization participation are recorded separately; no additional coauthor review is inferred.

## License

The Lean code and release documentation are offered under **Apache-2.0**, in [LICENSE](LICENSE). Third-party dependency licenses and retained source notices remain applicable. The manuscript is not distributed or licensed by this repository.
