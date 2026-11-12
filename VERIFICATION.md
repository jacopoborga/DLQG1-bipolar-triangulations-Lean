# Release verification

**The v0.1.0 core technical checks passed, and the author approved that reviewed archive.** This evidence is bound to that snapshot. The later Palomar integration has all ten intended local configurations complete, including Proposition 5.16 with a fresh normal source Comparator, both kernels and 55 axiom probes. The final official workflow still must pass all ten configurations at one exact final commit. Proposition 5.9 also has a historical individual official PASS at its listed earlier commit; neither fact replaces the final all-ten gate. Local and historical official results are summarized in [the current Palomar results](verification/PALOMAR-CURRENT-RESULTS.json). Source-domain bindings and rendering conventions are documented in [the deviations record](docs/ERRATA-AND-DEVIATIONS.md).

## Isolation and evidence reuse

The core source-only candidate was extracted into an isolated directory with **empty project build artifacts**. Pinned dependencies were restored and all **69,475 dependency files** SHA256-verified before and after the run. The project was built from source; historical project artifacts were not used.

Three additional source-domain verification modules were then compiled in a separate isolated directory using **41,530 individually hash-verified artifacts from that clean core run**. All 2,772 original Lean files and three configuration pins were byte-identical. The added proofs were freshly kernel-replayed through their entire transitive closure. The dependency files were again hash-verified before and after. This bounded continuation reuses successful evidence for unchanged inputs; it is not represented as a second full clean build.

## Reproduction

Install the pinned elan toolchain and obtain the dependencies at the revisions in `lake-manifest.json`, then run from the project root:

```bash
LEAN_NUM_THREADS=4 bash scripts/verify.sh
```

The core run used Lake’s supported package override for a verified metadata-free dependency cache, as described in README.md. The source-domain continuation used direct Lean commands with an explicit search path containing only its own output and those same verified dependencies. Neither route changes the pinned sources or project configuration. The shipped script provides the complete reader-facing sequence, including all three kernel checks.

## Results

| Check | Outcome |
|---|---|
| Public allowlist, hashes and import closure | PASS |
| Current manuscript correspondence | 90 entries; 97 primary paper exports |
| Lexical regression tests | 6 PASS |
| Core project build from source | Exit 0 |
| Wrapper, definition and correspondence axiom probes | 128 PASS |
| Direct implementation-export axiom probes | 98 PASS |
| Constant-window axiom probes | 3 PASS |
| Source-domain definitions and consumer proofs | 37 axiom probes PASS; all three added modules compile |
| Fresh kernel: `DirectedDistances.DeliveryVerificationRoot` | Exit 0; 107 semantic roots |
| Fresh kernel: `verification.ConstantWindowCheck` | Exit 0 |
| Fresh kernel: `verification.SourceScopeCheck` | Exit 0 |
| Dependency preservation, both stages | All 69,475 file hashes unchanged |

Only `propext`, `Classical.choice` and `Quot.sound` occur. [AXIOMS.json](verification/AXIOMS.json) lists every captured export and its axioms; probes can overlap. Style, deprecation and unused-variable warnings remain, without proof or kernel errors.

Core completion: **2026-11-11T06:48:44.102466Z**; core script elapsed **8058.39 seconds**. Source-domain continuation completed **2026-11-11T08:26:57.330726Z**. These are verification runs, not benchmarks.

## Exact input binding

The digest of sorted filenames and SHA256 values for all **2,775 Lean files and three configuration pins** is:

```text
476f882559c35f8d001ec2cdbd79689b1923fd24450961150513f39134d07a8d
```

[RESULTS.json](verification/RESULTS.json) records both stages, their compiler-input bindings, pin hashes, outcomes and log hashes. The current checker and added verification commands passed in the continuation. All original core compilation inputs remain unchanged. Documentation and receipts were finalized afterward and are covered by [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json).

[Independent release review](verification/REVIEW.md) separately addresses statement preservation, manuscript correspondence, exclusions, licenses and these receipts. Kernel replay checks formal proof terms; the correspondence argument establishes what those terms mean relative to the paper.

## Publication approval

The author approved publication of the reviewed archive with SHA256 `c250aace62d0d741c86696bbe036b35806e0a9aa72ba863e4c6a7048798733bb`. Publication changes only release documentation and the regenerated source manifest; every Lean source, pinned configuration and verification tool is byte-identical to the reviewed snapshot. Historical verification timestamps, outcomes, input bindings and `publication_authorized: false` in RESULTS.json describe the state when verification was recorded; they are preserved. See [PUBLICATION.md](PUBLICATION.md) for the subsequent approval.
