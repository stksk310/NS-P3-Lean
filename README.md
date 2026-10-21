# NS-P3/P4 Lean formalization

Public source repository for the NS-P3/P4 Lean formalization, software snapshot version **0.1.0**. For dated versions and archival identifiers, consult the [GitHub Releases](https://github.com/stksk310/NS-P3-Lean/releases) page and its corresponding Zenodo record, when available. This repository does not assert journal acceptance or independent human peer review of the associated manuscript.

This project formalizes the extremal minimal-presentation cardinality for numerical semigroups of actual embedding dimension four (the literature's shifted index e=3). For multiplicity m ≥ 4, the maximum is floor(2 + 2 sqrt(m)), and it is attained. At shifted index e=3, equality with the Macaulay bound occurs exactly for 4 ≤ m ≤ 9. The scope does not extend to arbitrary embedding dimension or classification of every attainable cardinality.

## Main declarations

| Result | Declaration | Source |
| --- | --- | --- |
| P3_MAIN | `NSP3.P3_MAIN` | `NSP3/P3Main.lean` |
| L12, attainment over the full spectrum | `NSP3.L12_P3_isGreatest` | `NSP3/L12Final.lean` |
| P4_e3, Macaulay equality range | `NSP3.P4_e3` | `NSP3/P4Final.lean` |

The frozen development contains historical `def ... : Prop` obligation statements and older partial-layer comments. Defining a proposition is not proving it. The current theorem declarations above, their proof bodies and referenced closure modules are the result interface. For example, `SymbolicFerrersObligations.lean` also contains explicit `_proof` theorems for its named obligations. Do not infer a theorem merely from an obligation's name or an old comment. `Main.lean` is preserved unchanged as a historical check driver; the root Lake library target is `NSP3`.

## Environment and reproduction

The frozen package version is **0.1.0**. Release tags, when present, identify archived snapshots; they do not alter the frozen source. It uses **Lean v4.34.0-rc1**, **472 frozen source/config files (467 Lean)** and **9 exact dependency Git pins**. The strict Lake setting `relaxedAutoImplicit = false` is unchanged. See [reproduction instructions](docs/REPRODUCIBILITY.md), [dependency pins](docs/DEPENDENCY_PINS.json), and [source manifest](docs/SOURCE_MANIFEST.sha256).

After provisioning the exact toolchain and pinned dependencies:

```sh
python -B docs/VERIFY_SOURCE.py .
python -B -O docs/VERIFY_SOURCE.py .
lake --no-cache build NSP3.P3Main NSP3.L12Final NSP3.P4Final
lake --no-cache build NSP3
lake env lean NSP3/P3FinalAxioms.lean
lake env lean NSP3/P4Axioms.lean
```

The accepted historical cold-recovery evidence covers 467 strict project-file checks, 866 axiom outputs and 33 axiom drivers with nine pinned dependencies. Its source manifest is `0a415b291f0c949651de72af2cf3f9dcffca8444b890b7131ee7577c1b649073`. The accepted cold RESULT SHA-256 is `5c2eb908c64f0e5a34a482cbf116d8d6005f20116a033b07e46a6b8f617cb5fe`; the author-decision R2 RESULT SHA-256 is `75d3cbdd7dd7098294c061da18644fde1178a32c3930a2a808cc30a95f98a049`. These identify existing evidence, not downloadable releases or DOIs. Full audit logs are retained separately. Installed Lean/stdlib was a trusted prebuilt baseline. **This metadata and public-visibility step does not rerun Lean, the cold build, or a kernel replay on another host.** Source hashes/API checks and a remote re-clone verify staging integrity, not a new mathematical proof.

## Attribution, authorship and licence

Keisuke Sato, Independent researcher, Japan; ORCID [0009-0005-4230-0268](https://orcid.org/0009-0005-4230-0268). The human author approved the mathematical text, attribution and substantive AI involvement. AI assistance contributed to research, proofs, Lean formalization, verification and writing; it is not represented as merely English polishing or human peer review.

The attainment families are credited to Elmacıoğlu and collaborators (2024); the prior support/staircase framework is credited to Brower–McDonough–O’Neill (2025). The associated manuscript's citations and 69-result/325-reference correspondence are preserved in [the map](docs/PROOF_TO_LEAN_MAP.json). Its manuscript paths and locations refer to the separately retained R2 paper package, which is not included in this source repository. No exhaustive priority or novelty clearance is asserted.

Original licensable Lean proofs and related original verification code use the unmodified official [Apache License 2.0](LICENSE), with [NOTICE](NOTICE). The author declares that these original project sources contain no copied third-party code and have no employer rights connection. This records the author's declaration, not an independent legal guarantee. Dependencies are not vendored and retain their own licences. See [rights/provenance scope](docs/RIGHTS_AND_PROVENANCE.md). The manuscript's publication licence is separate. Citation metadata for this software snapshot is in [CITATION.cff](CITATION.cff). For release-specific DOI and dates, consult the GitHub Releases page and its Zenodo archive record. Do not assume a release DOI from the repository URL alone.

## Historical diagnostics

The two frozen PowerShell scripts under `diagnostics/` are historical, host-specific audit drivers. **Do not run them directly as portable reproduction instructions.** They contain a fixed ELAN_HOME path and a broad Git trust setting. Read [the historical diagnostic notice](docs/HISTORICAL_DIAGNOSTICS.md) and use the portable commands in README and [REPRODUCIBILITY.md](docs/REPRODUCIBILITY.md). The scripts remain byte-identical to the frozen source authority.
