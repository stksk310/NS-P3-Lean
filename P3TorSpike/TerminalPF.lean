import P3TorSpike.AperyBasis
import NSP3.MinimalGeneratorClass
import NSP3.V03.BettiType

noncomputable section
namespace NSP3.TorSpike
open NSP3.V03

theorem minimalFour_generator_apery (m a b c g : ℕ)
    (h : MinimalFourGeneratorClass m a b c)
    (hg : g ∈ ([a,b,c] : List ℕ)) : g ∈ generatedApery m a b c := by
  have hat : SemigroupAtom (generatedSemigroup m a b c) g := h.atoms g (by simp_all)
  have hne : g ≠ m := by
    have hd := h.distinct
    simp only [List.nodup_cons, List.mem_cons] at hd hg
    aesop
  refine ⟨hat.1, Or.inr ?_⟩
  intro hsub
  have hge : m ≤ g := (minimalFour_multiplicity m a b c h).2.2 g hat.1 hat.2.1
  rcases hat.2.2 m (generatedSemigroup_generators m a b c).1 (g-m) hsub
    (by omega) with hz | hz
  · exact (Nat.ne_of_gt h.positive) hz
  · exact hne (by omega)

theorem terminal_ge_m (m a b c n : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (hn : TerminalApery m a b c n) : m ≤ n := by
  have hpos : 0 < n := by
    by_contra hz
    have he : n = 0 := by omega
    have ha := minimalFour_generator_apery m a b c a h (by simp)
    exact hn.2.1 (by simpa [he] using ha)
  exact (minimalFour_multiplicity m a b c h).2.2 n hn.1.1 hpos

abbrev TerminalIndex (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :=
  {p : AperyIndex m a b c hm hgcd // TerminalApery m a b c (aperyWeight a b c p.val)}

instance terminalIndexFintype (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Fintype (TerminalIndex m a b c hm hgcd) := Fintype.ofFinite _

def terminalPFEquiv (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    TerminalIndex m a b c h.positive h.coprime ≃ {f : ℕ // IsPseudoFrobenius m a b c f} := by
  have ha : 0 < a := lt_of_lt_of_le h.positive h.least_a
  have hb : 0 < b := lt_of_lt_of_le h.positive h.least_b
  have hc : 0 < c := lt_of_lt_of_le h.positive h.least_c
  apply Equiv.ofBijective (fun p => ⟨aperyWeight a b c p.val.val - m,
    terminal_sub_m_pseudoFrobenius m a b c _ h.positive ha hb hc
      (terminal_ge_m m a b c _ h p.property) p.property⟩)
  constructor
  · intro p q he
    apply Subtype.ext
    apply aperyExponent_injective m a b c h.positive h.coprime
    apply Subtype.ext
    have hp := terminal_ge_m m a b c _ h p.property
    have hq := terminal_ge_m m a b c _ h q.property
    have hh := congrArg Subtype.val he
    change aperyWeight a b c p.val.val = aperyWeight a b c q.val.val
    change aperyWeight a b c p.val.val-m = aperyWeight a b c q.val.val-m at hh
    omega
  · intro f
    have ht := pseudoFrobenius_add_m_terminal m a b c f.val h.positive ha hb hc f.property
    have hw := ht.1
    rw [generatedApery_eq_weights m a b c h.positive h.coprime] at hw
    obtain ⟨p,hp,he⟩ := hw
    refine ⟨⟨⟨p,hp⟩,by simpa [he] using ht⟩,?_⟩
    apply Subtype.ext
    change aperyWeight a b c p-m = f.val
    omega

theorem terminalIndex_card (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    Fintype.card (TerminalIndex m a b c h.positive h.coprime) = pseudoFrobeniusType m a b c := by
  classical
  rw [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (terminalPFEquiv m a b c h)]
  exact Nat.card_coe_set_eq _

end NSP3.TorSpike
