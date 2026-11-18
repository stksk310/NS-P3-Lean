import P3TorSpike.BinomialMinimality
import P3TorSpike.BinomialInterface
import P3TorSpike.BinomialVars
import P3TorSpike.BinomialSection
import P3TorSpike.BinomialTuple

#print NSP3.TorSpike.binomialIdeal_eq_ker
#print NSP3.TorSpike.relationConormal_finrank_eq_intrinsicRho
#print axioms NSP3.TorSpike.binomialIdeal_eq_ker
#print axioms NSP3.TorSpike.minimal_binomial_kernel_presentation
#print axioms NSP3.TorSpike.freeRelationMap_surjective
#print axioms NSP3.TorSpike.relationConormal_finite
#print axioms NSP3.TorSpike.conormalGenerator_linearIndependent
#print axioms NSP3.TorSpike.minimum_presentation_edge_indispensable
#print axioms NSP3.TorSpike.relationConormal_finrank_eq_intrinsicRho
#print axioms NSP3.TorSpike.relationConormal_mk_eq_zero
#print axioms NSP3.TorSpike.polynomialAugmentation_ker
#print axioms NSP3.TorSpike.polynomialMap_normalSection
#print axioms NSP3.TorSpike.relationKernel_le_augmentation
#print axioms NSP3.TorSpike.relationKernel_augmentationSubmodule_tuple

namespace NSP3.TorSpike

example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    Module.finrank ℚ (relationConormal ℚ m a b c) = intrinsicRho (generatedSemigroup m a b c) :=
  relationConormal_finrank_eq_intrinsicRho ℚ m a b c h

example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    Module.finrank (ZMod 2) (relationConormal (ZMod 2) m a b c) =
      intrinsicRho (generatedSemigroup m a b c) :=
  relationConormal_finrank_eq_intrinsicRho (ZMod 2) m a b c h

end NSP3.TorSpike
