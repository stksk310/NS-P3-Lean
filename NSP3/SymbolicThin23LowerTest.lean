import NSP3.SymbolicThin23Lower

namespace NSP3
-- Mutation caught: removing the exact universal lower-bound API.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1) :
    pair13Count S.D-2 ≤ (thin23LiftedColumns S g).card :=
  thin23_lifted_columns_lower S hg hf ho ht hs hy hz
end NSP3
