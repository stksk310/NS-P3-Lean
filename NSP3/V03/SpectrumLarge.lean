import NSP3.V03.SpectrumFamilies
import NSP3.V03.Boundary

namespace NSP3.V03

open NSP3.Sharpness

/-- Parity parameters for every prescribed cardinality at least six. -/
theorem spectrum_parameter_split (m q : ℕ) (hq : 6 ≤ q)
    (hbound : (q-2)^2 ≤ 4*m) :
    (∃ k, 1 ≤ k ∧ q=2*k+4 ∧ (k+1)^2 ≤ m) ∨
    (∃ k, 2 ≤ k ∧ q=2*k+3 ∧ k*k+k+1 ≤ m) := by
  by_cases he : q % 2=0
  · let k := (q-4)/2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hqk : q=2*k+4 := by dsimp [k]; omega
    have hs : q-2=2*k+2 := by omega
    left
    refine ⟨k,hk,hqk,?_⟩
    rw [hs] at hbound
    nlinarith
  · let k := (q-3)/2
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hqk : q=2*k+3 := by dsimp [k]; omega
    have hs : q-2=2*k+1 := by omega
    right
    refine ⟨k,hk,hqk,?_⟩
    rw [hs] at hbound
    nlinarith

/-- All-class necessity stated with the integer square root, independently of a construction. -/
theorem spectrum_member_upper {m q : ℕ} (hq : q ∈ sharpRhoValues m) :
    q ≤ 2+Nat.sqrt (4*m) := by
  rcases hq with ⟨S,hcof,hedim,hmult,hrho⟩
  obtain ⟨a,b,c,h,heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hmult
  have hset : generatedSemigroup m a b c = (S : Set ℕ) :=
    congrArg (fun T : AddSubmonoid ℕ => (T : Set ℕ)) heq
  rw [← hrho]
  simpa only [hset] using NSP3.V03.intrinsic_rho_sharp m a b c h

theorem spectrum_member_square_bound {m q : ℕ} (hq : q ∈ sharpRhoValues m) :
    (q-2)^2 ≤ 4*m := by
  have hu := spectrum_member_upper hq
  have hs : q-2 ≤ Nat.sqrt (4*m) := by omega
  simpa [pow_two] using (Nat.le_sqrt.mp hs)

/-- The actual even/odd numerical semigroups realize every allowed q>=6. -/
theorem spectrum_large_exists (m q : ℕ) (hq : 6 ≤ q)
    (hbound : (q-2)^2 ≤ 4*m) : q ∈ sharpRhoValues m := by
  rcases spectrum_parameter_split m q hq hbound with
    ⟨k,hk,hqk,hm⟩ | ⟨k,hk,hqk,hm⟩
  · have h := even_minimalFour m k hk hm
    have hs := minimal_generator_class_bridge m (evenA m k) (evenB m k) (evenC m k) h
    refine ⟨generatedAddSubmonoid m (evenA m k) (evenB m k) (evenC m k),
      hs.2.2.2,hs.2.2.1,hs.1,?_⟩
    change intrinsicRho (generatedSemigroup m (evenA m k) (evenB m k) (evenC m k))=q
    exact (even_family_rho_eq m k hk hm).trans hqk.symm
  · have h := odd_minimalFour m k hk hm
    have hs := minimal_generator_class_bridge m (oddA m k) (oddB m k) (oddC m k) h
    refine ⟨generatedAddSubmonoid m (oddA m k) (oddB m k) (oddC m k),
      hs.2.2.2,hs.2.2.1,hs.1,?_⟩
    change intrinsicRho (generatedSemigroup m (oddA m k) (oddB m k) (oddC m k))=q
    exact (odd_family_rho_eq m k hk hm).trans hqk.symm

/-- Exact large-cardinality portion of the attainable spectrum on the original intrinsic invariant. -/
theorem spectrum_large_iff (m q : ℕ) (hq : 6 ≤ q) :
    q ∈ sharpRhoValues m ↔ (q-2)^2 ≤ 4*m :=
  ⟨spectrum_member_square_bound, spectrum_large_exists m q hq⟩

end NSP3.V03
