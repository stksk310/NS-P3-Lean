import NSP3.SymbolicThinColumns

open NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    thin23LiftedColumns S g ⊆ S.D := thin23_lifted_columns_subset_D S hg hf
