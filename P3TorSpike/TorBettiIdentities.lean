import P3TorSpike.TorReducedBetti
import P3TorSpike.KoszulRelationsH1
import P3TorSpike.BinomialMinimality

noncomputable section
namespace NSP3.TorSpike

/-- First total Betti number equals the intrinsic minimal presentation cardinality. -/
theorem torBetti_one (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    torBetti k m a b c 1 = intrinsicRho (generatedSemigroup m a b c) :=
  (Koszul.torOneConormalFieldIso k m a b c h).toLinearEquiv.finrank_eq.trans
    (relationConormal_finrank_eq_intrinsicRho k m a b c h)

/-- The actual total Betti sequence, with no Tor or rank certificate assumptions. -/
theorem torBetti_identities (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    torBetti k m a b c 0 = 1 ∧
    torBetti k m a b c 1 = intrinsicRho (generatedSemigroup m a b c) ∧
    torBetti k m a b c 2 = intrinsicRho (generatedSemigroup m a b c) +
      NSP3.V03.pseudoFrobeniusType m a b c - 1 ∧
    torBetti k m a b c 3 = NSP3.V03.pseudoFrobeniusType m a b c ∧
    ∀ n, 4 ≤ n → torBetti k m a b c n = 0 := by
  have h₁ := torBetti_one k m a b c h
  have h₃ := torBetti_three k m a b c h
  have hmid := torBetti_middle k m a b c h
  refine ⟨torBetti_zero k m a b c h, h₁, ?_, h₃, ?_⟩
  · omega
  · exact torBetti_from_four k m a b c

/-- In this embedding-dimension-four class the actual total Betti numbers
are independent of the coefficient field, including its characteristic. -/
theorem torBetti_field_independent (k l : Type) [Field k] [Field l] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (n : ℕ) :
    torBetti k m a b c n = torBetti l m a b c n := by
  have hk := torBetti_identities k m a b c h
  have hl := torBetti_identities l m a b c h
  rcases n with _ | _ | _ | _ | n
  · exact hk.1.trans hl.1.symm
  · exact hk.2.1.trans hl.2.1.symm
  · exact hk.2.2.1.trans hl.2.2.1.symm
  · exact hk.2.2.2.1.trans hl.2.2.2.1.symm
  · rw [torBetti_from_four k m a b c (n+4) (by omega),
      torBetti_from_four l m a b c (n+4) (by omega)]

end NSP3.TorSpike
