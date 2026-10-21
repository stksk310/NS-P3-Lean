# Source integrity and Lean reproduction

The project root contains lakefile.toml, lean-toolchain and lake-manifest.json. Preserve their exact bytes. The source manifest lists only the 472 frozen source/config files; additional staging metadata is recorded in the separate private-staging evidence package.

For byte-exact Windows checkouts, use `git -c core.autocrlf=false clone <the actual authorized repository URL>`. The staging and verification clones use core.autocrlf=false. A default Git newline conversion can otherwise change working-tree hashes even when blob bytes are unchanged.

Run `python -B docs/VERIFY_SOURCE.py .` and `python -B -O docs/VERIFY_SOURCE.py .` for the 472-file manifest, nine pins, 69 result records and 325 source-declaration references. This script uses only the Python standard library and does not invoke Lean. The full repository inventory also includes documentation and citation/licence metadata.

Install the exact Lean toolchain named in lean-toolchain. Provision the exact nine dependency revisions in docs/DEPENDENCY_PINS.json and lake-manifest.json. The Lake require entry is not permission to update the resolved pins. A first network-dependent setup may fetch those sources; an offline rebuild requires pre-provisioned pinned dependencies and the installed toolchain. Do not claim an empty-machine offline build from this source-only repository alone.

From a fresh workspace without project/dependency build products, use:

```sh
lake --no-cache build NSP3.P3Main NSP3.L12Final NSP3.P4Final
lake --no-cache build NSP3
lake env lean NSP3/P3FinalAxioms.lean
lake env lean NSP3/P4Axioms.lean
```

For strict per-file checking, every project Lean file must be checked under the frozen Lake options, including relaxedAutoImplicit=false, with dependencies in topological order. Merely checking selected main targets is not a repeat of the historical all-467-file strict audit. Individual axiom outputs in that accepted evidence used only propext, Classical.choice and Quot.sound, or no axioms. Rerun and retain actual outputs before making a new axiom/rebuild claim.

Historical accepted receipts (not rerun in this staging phase): 467 strict file checks, 866 axiom outputs, 33 drivers, nine pins, inherited installed Lean/stdlib baseline. The R2 and cold archive SHA identifiers are in README. Hash checks and a same-host remote clone do not constitute independent human refereeing or a separate-host Lean kernel replay. The private-staging phase intentionally does not run a new Lean smoke/build test.

Frozen historical diagnostic scripts in `diagnostics/` retain a host-specific ELAN_HOME setting and their original Git trust setting. They are included unchanged to preserve the 472-file source authority, not executed by this private-staging workflow. Use the portable commands above with your own environment. Review the two inherited host-path strings before any future public visibility change; this snapshot does not certify that every frozen file is free of host-specific text.
