import P3TorSpike.RegularReductionSemigroup

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NSP3.TorSpike.RegularReduction
open CategoryTheory

variable (k R : Type) [Field k] [CommRing R] [Algebra k R]

/-- A regular first variable makes the four-variable top Koszul differential injective. -/
theorem regularTop_injective (t : R) (u : Fin 3 → R)
    (ht : Function.Injective (multiply k R t)) :
    Function.Injective (coneIncoming (threeH3Complex k R u) (multiplyH3 k R t u)) := by
  rintro ⟨x,z⟩ ⟨y,w⟩ h
  apply Prod.ext
  · apply ht
    have h₂ := congrArg Prod.snd h
    change multiply k R t x + 0 = multiply k R t y + 0 at h₂
    simpa only [add_zero] using h₂
  · change (z : Fin 0 → R) = w
    funext i
    exact Fin.elim0 i

theorem regularTop_kernel (t : R) (u : Fin 3 → R)
    (ht : Function.Injective (multiply k R t)) :
    LinearMap.ker (coneIncoming (threeH3Complex k R u) (multiplyH3 k R t u)) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (regularTop_injective k R t u ht)

theorem semigroupTop_kernel (m a b c : ℕ) :
    LinearMap.ker (coneIncoming
      (threeH3Complex k (SemigroupRing k m a b c) (semigroupParameters k m a b c))
      (multiplyH3 k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)
        (semigroupParameters k m a b c))) = ⊥ :=
  regularTop_kernel k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)
    (semigroupParameters k m a b c) (semigroupMultiplicity_regular k m a b c)

end NSP3.TorSpike.RegularReduction
