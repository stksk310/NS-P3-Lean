import P3TorSpike.KoszulRelationsH1
import P3TorSpike.BinomialMinimality

#print axioms NSP3.TorSpike.Koszul.semigroupKoszulH1EquivConormal
#print axioms NSP3.TorSpike.Koszul.torOneConormalFieldIso
#print axioms NSP3.TorSpike.Koszul.relationCycleClass_exact
#print axioms NSP3.TorSpike.Koszul.relationCycleClass_surjective
#check NSP3.TorSpike.Koszul.semigroupKoszulH1EquivConormal
#check NSP3.TorSpike.Koszul.torOneConormalFieldIso

example (k : Type) [Field k] (m a b c : ℕ)
    (h : NSP3.MinimalFourGeneratorClass m a b c) :
    Module.finrank k ((NSP3.TorSpike.semigroupKoszulComplex k m a b c).homology 1) =
      NSP3.intrinsicRho (NSP3.generatedSemigroup m a b c) := by
  exact (NSP3.TorSpike.Koszul.semigroupKoszulH1EquivConormal k m a b c h).finrank_eq.trans
    (NSP3.TorSpike.relationConormal_finrank_eq_intrinsicRho k m a b c h)
