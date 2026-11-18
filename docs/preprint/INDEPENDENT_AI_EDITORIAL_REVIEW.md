# Separate-context AI editorial review, 18 November 2026

The final preprint source has no open actionable findings in this limited editorial review. The reviewer was a separate Codex agent working on the author's side. The review covered the editorial diff, the theorem and proof-route descriptions, the execution and availability disclosures, and the AI attribution. Mathematical refereeing, fresh Lean execution, live release-link checks and rendered-PDF inspection were outside this review.

## Finding and resolution

**Minor, resolved.** The previous candidate at SHA-256 `17bc4918c374f37a1a4e8852ae3343148851b610ec8caa55b6fbd9fa836df151` said the supplement contained “pinned dependencies.” The supplement supplies nine dependency entries in its Lake manifest and an explicit Lean toolchain pin. Its NOTICE describes the external libraries as unbundled. The final source says “dependency pins.”

## Checks on the final source

- Direct byte comparison gave identical results for the entire mathematical body, from the introduction through the last proof, and for the bibliography through end of file. The Chomicz citation and both bibliography entries retain their adopted text and targets. The only abstract edit removes the sentence identifying the narrow-width proof cases. Both case subsections and their proofs remain in place. A freshly generated unified diff matched the supplied patch byte for byte.
- The preserved V03 endpoint checks give the exact extremal formula, the complete attainable spectrum and the Macaulay equality criterion. The public Betti entry point uses the invariant defined by scalar-restricted finite rank of the semigroup algebra's categorical Tor with the polynomial residue field. Its signatures use `(k : Type) [Field k]` and show the tuple, all-degree finiteness, sharpness-family realization and the two windows. The final log includes actual Tor-object vanishing from degree four and the conormal and degree-three comparisons. The preprint's field-universe qualifier matches these signatures. It reports bounded windows and gives no full classification of Betti tuples.
- The manuscript identifies the alternate proof for its staircase socle lemma. The Lean corner theorem assumes a nonempty finite downset and bounds the maximal-point count by the two minimal-complement counts using a slice argument. The disclosure describes formalized results and acknowledges proof-route differences.
- The dated final receipt reports successful new-module execution against the matching V03 baseline and cached dependency objects. Its output records 17 axiom closures, each consisting of `propext`, `Classical.choice` and `Quot.sound`. The preprint accurately limits the replay claim. Its public archive links refer to historical v0.1.0. Current sources, a theorem map, dependency pins and execution records are present in the local supplement. The text assigns no public URL to the new materials.
- The author line names Keisuke Sato. The declaration identifies ChatGPT and Codex, explicitly describes substantial contributions to research, proof construction, Lean, verification and writing, and assigns responsibility to the author. It identifies the AI checks as author-side work. The changes introduce no journal attribution, coauthor, endorsement, private correspondence or independent human-review claim.

## Inspected SHA-256 values

Paths below use the Problem3Lean workspace as root. The `project/`, `review/` and `logs/` paths are relative to `tor_completion_20261116/`. Each listed file under these three directories also matched its member of the current supplement byte for byte.

| Object | SHA-256 |
| --- | --- |
| `manuscript_improvement_v03_20261115/result/manuscript/PAPER_V03.tex` | `38aec56109a57b0aa523ab35e6d219b6a249f6d980278cfab8a3770618226db9` |
| `preprint_p3_20261118/manuscript/P3_PREPRINT.tex` | `d859ce510fac13a6900c75e1db05985b990b462c436a827442b81369df81fcbd` |
| `preprint_p3_20261118/audit/EDITORIAL_DIFF.patch` | `51ea14a7a701144f6c97be3f3d8a25368c085f605732c436125ccaae98e8023a` |
| Mathematical body, 62,522 bytes in each TeX file | `1c75f2285d0b170fd672945ceb5ca31deaf043ffb1243b24d06f240e89a94a1d` |
| Bibliography through end of file, 1,715 bytes in each TeX file | `7341b553f56e09683d90a7974643484b38e59a8b8f6f6de7171d3ad95217cd7c` |
| `NS_P3_TOR_BETTI_COMPLETION_20261116.zip` | `ce5ce71cb201b7f122223ea49d2a23120133dd5faefe2068cf667d6e4a34cfb8` |
| `review/RESULT.json` | `0f7dcff208d5bcd17f30e9d5ddbe56349a2324435ab068cbd8594acc9133dd8d` |
| `review/PAPER_LEAN_MAP.md` | `320d6725a0b01d59a433f303d6d06520c972b17f15038bf85a26c2b5d24abd68` |
| `project/P3Betti.lean` | `ad7a6d31857c4a5bec45b9367792d1c51c1910cf6a8933610ea38a4a92c36597` |
| `project/P3TorSpike/TorObjects.lean` | `ed9deed5efbb484f52ffd67cb16d7869b563d846c8d66fd2ae593088d0acc739` |
| `project/P3TorSpike/TorBettiDefinitions.lean` | `57d09cf65fde6c78613058c5e9c941405adf6d6412a65f575392b44b88ecfce3` |
| `project/P3TorSpike/FinalChecks.lean` | `04f4e75e1ff12ecb3d7b0ab9b23407bfa35187d6b731353f99b44c77196dd46b` |
| `logs/20261116_222055_970_P3TorSpike_FinalChecks.json` | `786458c53eada22aba5f74843606d5670d663848d21f55e9a81a3a2c21072ef0` |
| `logs/20261116_222055_970_P3TorSpike_FinalChecks.log` | `576617d02e06af589d534bda91ca7c85520af8174c0f7e7a4aa777d6f48898e3` |
| `project/NSP3/V03/FinalChecks.lean` | `f16b3d124c943133f00db8fb7ed5100ad162d2b063a18c29cd1f16f5cdbb2207` |
| `project/NSP3/V03/CornerBound.lean` | `86faa401babf89eb91c401cbf382284fc852c690e0e2d9ce45adc55ddf4e0656` |
| `project/lean-toolchain` | `cdbc6c372a2b37ad94430a6cec69cedfa4d36f255bfd968773fd91bf7a1746bf` |
| `project/lake-manifest.json` | `d868f19bc1d0c6f095ca0166d2a771e79265582181f5fc916478613b2fc6606a` |
| `project/LICENSE` | `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` |
| `project/NOTICE` | `7706a0877bcb8b20b6f7dd95d05a750df0cde9d7bf9e2288573a93e539160366` |
