import P3TorSpike.KoszulResolution

#print axioms NSP3.TorSpike.Koszul.resolution
#print axioms NSP3.TorSpike.Koszul.contraction_identity
#print axioms NSP3.TorSpike.Koszul.exact_positive
#print axioms NSP3.TorSpike.Koszul.exact_zero
#check NSP3.TorSpike.Koszul.resolution
#check NSP3.TorSpike.Koszul.gradedEquiv
#check NSP3.TorSpike.Koszul.complex_exactAt_succ

example (k : Type) [Field k] (n : ℕ) :
    CategoryTheory.Projective ((NSP3.TorSpike.Koszul.resolution k).complex.X n) := inferInstance
