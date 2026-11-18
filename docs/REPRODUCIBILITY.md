# Reproduction and evidence: v0.2.0

The current source authority is the `project/` tree in `NS_P3_TOR_BETTI_COMPLETION_20261116.zip`, not the older repository root from v0.1.0. All 575 Lean files, the toolchain, Lake configuration, and dependency manifest are copied byte for byte. The internal Lake package version `0.0.1` is preserved as part of this configuration; the scholarly software release is v0.2.0.

The release provides:

- `P3_PREPRINT.pdf`: the 21-page manuscript dated 18 November 2026.
- `P3_PREPRINT_SOURCE_20261118.zip`: TeX and build instructions.
- `NS_P3_PREPRINT_20261118.zip`: frozen paper, scripts, editorial/PDF checks, and the unchanged Lean supplement.
- `NS_P3_TOR_BETTI_COMPLETION_20261116.zip`: source, original execution receipts/logs, manifest and read-only verifier.
- `PUBLICATION_SHA256SUMS.txt`: hashes of the release files.

For a new environment, use the commands in the root README. They are portable intended build commands, not a claim of a completed dependency-cold build during publication. Never run `lake update` to replace the pinned dependency revisions. For the frozen supplement, its `replay_new.ps1` accepts explicit dependency-package and matching-source V03 baseline library paths and creates new timestamped receipts. Its default paths are host-specific. The original `run_lean.ps1` runner preserves existing receipts. Some historical successful executions had no stdout file; the existing `stdout_file_present` field states that fact rather than inventing logs.

The Tor completion's existing evidence covers 52 added Lean files, 523 preserved baseline files and 17 principal standard-axiom closures. It uses a matching-source warm baseline and cached dependencies on the same host. It is not a full dependency-cold rebuild or an independent-host check. The formal proofs use genuine categorical Tor, finite-dimensionality and explicit Koszul/conormal/socle comparisons. Their scope is all fields of carrier Type0, arbitrary characteristic.

`docs/tor/RESULT.json` and the preserved scope map retain their original paths relative to the frozen supplement, where the referenced logs and files can be found. They are not newly generated publication receipts. The preprint editorial/PDF checks under `docs/preprint/` likewise retain their original preprint-package context. The source-map manuscript SHA refers to V03; the preprint body and bibliography are identical and only its front matter/disclosures changed.

`tools/verify_publication.py` checks this checkout's release manifest, all 575 source identities, exact dependency pins and the manuscript hash. It is read-only and works under `python -O`. It does not execute Lean. The finite-check scripts are also read-only in their normal mode and must receive `--source manuscript/P3_PREPRINT.tex`.

Historical v0.1.0 documentation and its verifier are stored under `docs/historical/v0.1.0/`; run that verifier only against the unchanged v0.1.0 checkout. Old manuscript line numbers and old numerical counts do not describe this release.
