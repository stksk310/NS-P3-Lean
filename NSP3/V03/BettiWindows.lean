import NSP3.V03.BettiTypeFamilies
import NSP3.V03.BettiType
import NSP3.V03.SpectrumLarge

/-! Simultaneous presentation/PF realizations, with no assertion about Tor. -/

namespace NSP3.V03

open NSP3.Sharpness

theorem even_numeric_pseudoFrobenius_card (m k : ℕ)
    (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) (hpos : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd (evenA m k)
      (Nat.gcd (evenB m k) (evenC m k)))=1) :
    (pseudoFrobeniusFinset m (evenA m k) (evenB m k) (evenC m k)
      hpos hgcd).card=2*k+1 := by
  let L := m-k*k-k
  have ht : k*k+2*k+1 ≤ m := by nlinarith
  have hL : k<L := by dsimp [L]; omega
  have hrel : L+k*k+k=m := by dsimp [L]; omega
  have ha : evenA m k+1=(k+1)*m := by
    have : 0<(k+1)*m := Nat.mul_pos (by omega) hpos
    unfold evenA
    omega
  exact even_family_pseudoFrobenius_card m k L _ _ _ hk hL hrel ha rfl rfl hgcd

theorem odd_numeric_pseudoFrobenius_card (m k : ℕ)
    (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) (hpos : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd (oddA m k)
      (Nat.gcd (oddB m k) (oddC m k)))=1) :
    (pseudoFrobeniusFinset m (oddA m k) (oddB m k) (oddC m k)
      hpos hgcd).card=2*k := by
  let L := m-k*k-1
  have hL : k≤L := by dsimp [L]; omega
  have hrel : L+k*k+1=m := by dsimp [L]; omega
  have ha : oddA m k+1=k*m := by
    have : 0<k*m := Nat.mul_pos (by omega) hpos
    unfold oddA
    omega
  exact odd_family_pseudoFrobenius_card m k L _ _ _ hk hL hrel ha rfl rfl hgcd

/-- Every large admissible presentation cardinality has an actual family of type q-3. -/
theorem presentation_pseudoFrobenius_window (m q : ℕ) (hq : 6≤q)
    (hbound : (q-2)^2≤4*m) :
    ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c,
      intrinsicRho (generatedSemigroup m a b c)=q ∧
      (pseudoFrobeniusFinset m a b c h.positive h.coprime).card=q-3 := by
  rcases spectrum_parameter_split m q hq hbound with
    ⟨k,hk,hqk,hm⟩ | ⟨k,hk,hqk,hm⟩
  · let h := even_minimalFour m k hk hm
    refine ⟨evenA m k,evenB m k,evenC m k,h,?_,?_⟩
    · exact (even_family_rho_eq m k hk hm).trans hqk.symm
    · have ht := even_numeric_pseudoFrobenius_card m k hk hm h.positive h.coprime
      omega
  · let h := odd_minimalFour m k hk hm
    refine ⟨oddA m k,oddB m k,oddC m k,h,?_,?_⟩
    · exact (odd_family_rho_eq m k hk hm).trans hqk.symm
    · have ht := odd_numeric_pseudoFrobenius_card m k hk hm h.positive h.coprime
      omega

/-- The same existence result on the cardinality of the actual PF set. -/
theorem presentation_type_window (m q : ℕ) (hq : 6≤q)
    (hbound : (q-2)^2≤4*m) :
    ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c,
      intrinsicRho (generatedSemigroup m a b c)=q ∧
      pseudoFrobeniusType m a b c=q-3 := by
  obtain ⟨a,b,c,h,hrho,htype⟩ :=
    presentation_pseudoFrobenius_window m q hq hbound
  refine ⟨a,b,c,h,hrho,?_⟩
  rw [pseudoFrobeniusType_eq_finset_card m a b c h.positive
    (by have := h.least_a; have := h.positive; omega)
    (by have := h.least_b; have := h.positive; omega)
    (by have := h.least_c; have := h.positive; omega) h.coprime]
  exact htype

end NSP3.V03
