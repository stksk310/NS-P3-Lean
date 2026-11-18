# Manuscript / Lean map for the completed Betti layer

Frozen manuscript SHA256: `38aec56109a57b0aa523ab35e6d219b6a249f6d980278cfab8a3770618226db9`.

| Mathematical claim | Checked public theorem / construction |
| --- | --- |
| Actual polynomial map onto the semigroup algebra | `NSP3.TorSpike.polynomialMap_surjective` (unchanged spike base) |
| Genuine polynomial residue-field free resolution | `NSP3.TorSpike.Koszul.resolution` |
| Genuine categorical Tor computed by actual Koszul complex | `NSP3.TorSpike.torKoszulFieldIso` |
| Tor₁ identified with the actual relation conormal | `NSP3.TorSpike.Koszul.torOneConormalFieldIso` |
| Actual conormal dimension equals minimal monoid presentation size | `NSP3.TorSpike.relationConormal_finrank_eq_intrinsicRho` |
| Regular multiplicity monomial / reduced complex | `NSP3.TorSpike.RegularReduction.semigroupKoszulH1Equiv`, `semigroupKoszulH2Equiv`, `semigroupKoszulH3Equiv` |
| Actual terminal Apéry basis of the socle | `NSP3.TorSpike.socleBasis`, `socle_finrank_eq_type` |
| All actual Tor spaces finite, cardinal dimension = numerical Betti | `NSP3.Betti.finite`, `NSP3.Betti.dimension_eq_total` |
| Total Betti identity and degree≥4 vanishing | `NSP3.Betti.identities` |
| Simultaneous upper bounds / no-full improvement | `NSP3.Betti.upper`, `NSP3.Betti.noFull_upper` |
| Known-family total Betti tuples | `NSP3.Betti.realized` |
| Attained extremal windows | `NSP3.Betti.maximumSecond_window`, `NSP3.Betti.maximumThird_window`; `maximumTorBetti2_attained`, `maximumTorBetti3_attained` |
| Field/characteristic independence | `NSP3.Betti.field_independent` |

The field carrier is Type0, exactly as stated in each final signature. The numerical-semigroup class uses actual atoms, generated semigroup membership, multiplicity and coprimality; it is not an arbitrary staircase certificate. Existing `numerical_semigroup_class_coverage` covers the cofinite embedding-dimension-four submonoid class. The β₃ value-set equality in `TorBettiExtrema.lean` checks both directions of this coverage explicitly.

The generic corner bound uses the previously proved combinatorial slice argument. The new Tor layer uses a concrete characteristic-independent Koszul contraction and explicit cycle/boundary comparisons; it does not formalize every sentence of the paper's Scarf-deformation proof. Main statements are connected to the original mathematical objects by proved maps.

The existing complete-spectrum/P3/P4 sources are preserved. The new work fills the formerly excluded Tor/total-Betti layer; it does not claim exact maxima, classification of all Betti tuples, graded Betti-degree classification, a new semigroup family, or publication approval.
