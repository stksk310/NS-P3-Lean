# P3 preprint version 4 (R18)

- [Read the 28-page preprint](P3_EDITORIAL_R18.pdf)
- [TeX source](P3_EDITORIAL_R18.tex)
- [Source ZIP with Lean and finite-verification materials](P3_ARXIV_SOURCE_R18.zip)
- [Version 4 on Zenodo](https://doi.org/10.5281/zenodo.24370007)
- [Software v0.2.0 on Zenodo](https://doi.org/10.5281/zenodo.24346459)
- [Previous preprint version (R07)](../v3-r07/)

This revision includes the comparison with the Elias–Geramita–Valla
type bound for four generators and a direct proof of the staircase socle
bound. It clarifies the finite certificates, references and AI-use
disclosure and adds Lean statement excerpts to the appendix.

The [appendix replay](APPENDIX_LEAN_EXTENDED.json) checks the two theorem
statements printed in the R18 appendix against the archived Lean declarations.
It uses the pinned Lean 4.34.0-rc1 toolchain, pinned dependencies and
receipt-matched project oleans. The [test](AppendixR18.lean) and
[output](APPENDIX_LEAN_EXTENDED.txt) accompany the receipt. Its scope is
the appendix excerpts checked in that environment.

The manuscript is licensed under CC BY 4.0. Original companion code is
licensed under Apache 2.0. See the notices in the source ZIP.
