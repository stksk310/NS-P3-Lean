import NSP3.V03
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective

#check AddMonoidAlgebra.mapDomainAlgHom
#check AddMonoidAlgebra.mapDomain_injective
#check AddMonoidAlgebra.single_mul_single
#check AddMonoidAlgebra.single_pow
#check AddMonoidAlgebra.induction_on
#check MvPolynomial.aeval
#check MvPolynomial.aeval_X
#check MvPolynomial.constantCoeff
#check CategoryTheory.Tor
#check ModuleCat.of
#check Module.compHom
#check RingHom.toAlgebra
#check Finsupp.mapDomain_injective
noncomputable section

example (k : Type) [Field k] (m a b c : ℕ) :
    CommRing (AddMonoidAlgebra k (NSP3.generatedAddSubmonoid m a b c)) := inferInstance

example (k : Type) [Field k] (m a b c : ℕ) :
    IsDomain (AddMonoidAlgebra k (NSP3.generatedAddSubmonoid m a b c)) := inferInstance

example (k : Type) [Field k] :
    CategoryTheory.HasProjectiveResolutions (ModuleCat (MvPolynomial (Fin 4) k)) := inferInstance
