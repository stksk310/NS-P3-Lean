import P3TorSpike.SocleBasic
import P3TorSpike.TerminalPF

noncomputable section
namespace NSP3.TorSpike
open NSP3.V03

theorem socle_coordinate_zero (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (f : Reduction k m a b c) (hf : f ∈ socle k m a b c)
    (p : AperyIndex m a b c hm hgcd)
    (hp : ¬ TerminalApery m a b c (aperyWeight a b c p.val)) :
    (aperyBasis k m a b c hm hgcd).repr f p = 0 := by
  classical
  have hap := canonical_weight_mem_generatedApery m a b c hm
    ((mem_aperyStandardSet m a b c hm hgcd p.val).mp p.property)
  have hnot := (terminal_iff_all_shift_not_apery m a b c _ hap).not.mp hp
  push Not at hnot
  obtain ⟨i,hi⟩ := hnot
  apply annihilated_coordinate_zero k m a b c hm hgcd
    (nonmultiplicityGenerator m a b c i) f (hf i) p
  exact hi

def terminalVector (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : TerminalIndex m a b c hm hgcd) : Reduction k m a b c :=
  aperyVector k m a b c hm hgcd p.val

theorem terminalVector_mem_socle (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : TerminalIndex m a b c hm hgcd) :
    terminalVector k m a b c hm hgcd p ∈ socle k m a b c := by
  intro i
  rw [terminalVector,reducedGenerator,reduced_mul_aperyVector]
  apply outside_apery_killed
  exact (terminal_iff_all_shift_not_apery m a b c _ p.property.1).mp p.property i

theorem socle_eq_terminal_span (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    socle k m a b c = Submodule.span k (Set.range (terminalVector k m a b c hm hgcd)) := by
  classical
  apply le_antisymm
  · intro f hf
    rw [← (aperyBasis k m a b c hm hgcd).sum_repr f]
    apply Submodule.sum_mem
    intro p hp
    by_cases ht : TerminalApery m a b c (aperyWeight a b c p.val)
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨⟨p,ht⟩,by simp [terminalVector]⟩
    · rw [socle_coordinate_zero k m a b c hm hgcd f hf p ht,zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    exact terminalVector_mem_socle k m a b c hm hgcd p

theorem terminalVectors_independent (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    LinearIndependent k (terminalVector k m a b c hm hgcd) :=
  (aperyVectors_independent k m a b c hm hgcd).comp
    (fun p : TerminalIndex m a b c hm hgcd => p.val) Subtype.val_injective

/-- The actual terminal monomials form a basis of the simultaneous annihilator. -/
def socleBasis (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Module.Basis (TerminalIndex m a b c hm hgcd) k (socle k m a b c) :=
  (Module.Basis.span (terminalVectors_independent k m a b c hm hgcd)).map
    (LinearEquiv.ofEq _ _ (socle_eq_terminal_span k m a b c hm hgcd).symm)

@[simp] theorem socleBasis_apply (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : TerminalIndex m a b c hm hgcd) :
    (socleBasis k m a b c hm hgcd p : Reduction k m a b c) =
      terminalVector k m a b c hm hgcd p := by
  simp [socleBasis]

theorem socle_finite (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Module.Finite k (socle k m a b c) :=
  Module.Finite.of_basis (socleBasis k m a b c hm hgcd)

theorem socle_finrank_eq_type (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    Module.finrank k (socle k m a b c) = pseudoFrobeniusType m a b c := by
  rw [Module.finrank_eq_card_basis (socleBasis k m a b c h.positive h.coprime)]
  exact terminalIndex_card m a b c h

end NSP3.TorSpike
