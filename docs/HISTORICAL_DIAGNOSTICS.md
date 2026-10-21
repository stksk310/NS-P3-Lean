# Historical PowerShell diagnostics — deprecated for direct reproduction

The immutable files `diagnostics/verify_symbolic.ps1` and `diagnostics/verify_symbolic_all_modules.ps1` are retained as historical audit drivers. **Do not execute these two scripts directly as current, portable reproduction instructions.** Their inclusion is not a recommendation to copy their environment or Git trust settings.

Both scripts hard-code `ELAN_HOME` to `C:/Users/stksk/.elan`. That path is a historical author-machine location, not a secret credential and not a requirement for other users. Both also set process-level Git configuration using `GIT_CONFIG_COUNT`, `GIT_CONFIG_KEY_0=safe.directory`, and `GIT_CONFIG_VALUE_0=*`. The wildcard broadly bypasses Git's ownership/trust check for commands in that environment. Do not adopt it as a portable security setting or run untrusted checkouts because of it. The scripts set process environment variables; this notice does not claim they permanently rewrite a user's global Git configuration file.

The frozen source/config payload contains 472 files. These two files have not been edited, sanitized, executed, removed or re-signed during publication preparation. Preserve their exact bytes when verifying the frozen source manifest. A Windows path string and historical broad trust setting are documented exceptions to the path scan, not evidence of a credential leak. Other unevaluated private paths or credentials must stop publication.

## Portable alternatives

Use your own correctly installed toolchain environment and a checkout you trust. Follow [README](../README.md) and [REPRODUCIBILITY.md](REPRODUCIBILITY.md). If Git reports dubious ownership, inspect the checkout and use a directory-specific trust decision instead of a wildcard. Preserve exact Git dependency pins and source line endings.

```sh
python -B docs/VERIFY_SOURCE.py .
python -B -O docs/VERIFY_SOURCE.py .
lake --no-cache build NSP3.P3Main NSP3.L12Final NSP3.P4Final
lake --no-cache build NSP3
lake env lean NSP3/P3FinalAxioms.lean
lake env lean NSP3/P4Axioms.lean
```

The source/API verifier checks integrity and source correspondence; it does not execute Lean. The above Lean commands are instructions for a future real rebuild. They were not executed during this metadata/visibility transition, and selected targets are not a repeat of the historical 467-file strict audit. This repository contains no newly asserted human peer review, tagged release, Zenodo deposit, DOI or journal submission.
