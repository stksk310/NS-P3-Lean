import NSP3.SymbolicBWPressure

namespace NSP3

/-- A uniform unbounded-coordinate branch, obtained from real diagonal injections.
The threshold is a proved sufficient condition, never a theorem hypothesis cap. -/
theorem bw_large_coordinate_pressure (r s t K L A B C : ℕ)
    (ht : 1 ≤ t) (hs : t ≤ s) (hr : s ≤ r)
    (ha : 1 ≤ A) (hb : 1 ≤ B) (hc : 1 ≤ C) (hk : K+r+s ≤ L+17)
    (hlarge : 7 ≤ A ∨ 7 ≤ B ∨ 7 ≤ C) :
    K ≤ max (A*B*C-1) L+ferrersPlaneDefect r A B+
      ferrersPlaneDefect s A C+ferrersPlaneDefect t B C := by
  have h12 := ferrersRectangle_diagonal_lower r A B (by omega) ha hb
  have h13 := ferrersRectangle_diagonal_lower s A C (by omega) ha hc
  have h23 := ferrersRectangle_diagonal_lower t B C ht hb hc
  have d12 : (ferrersRectangle r A B).card ≤ ferrersPlaneDefect r A B :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have d13 : (ferrersRectangle s A C).card ≤ ferrersPlaneDefect s A C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have d23 : (ferrersRectangle t B C).card ≤ ferrersPlaneDefect t B C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have o12 : 1 ≤ ferrersPlaneDefect r A B := le_max_left _ _
  have o13 : 1 ≤ ferrersPlaneDefect s A C := le_max_left _ _
  have o23 : 1 ≤ ferrersPlaneDefect t B C := le_max_left _ _
  have hm := le_max_right (A*B*C-1) L
  rcases hlarge with h | h | h <;> omega

/- Six small endpoints remain after the shared unbounded-height quadratic proof.
Large coordinates are proved ABOVE. Inside the complementary small corner,
only the general W interval/rectangle inequalities and one exact W(4,1,1)
value are used. This is not a69-profile staircase checker or an added g cap. -/
set_option maxHeartbeats 8000000 in
private theorem six_pressure (r s t K L A B C : ℕ)
    (ha : 1 ≤ A) (hb : 1 ≤ B) (hc : 1 ≤ C) (hcap : r+2 ≤ A+B+C)
    (hq : (r=6 ∧ s=4 ∧ t=4 ∧ K=18 ∧ L=13) ∨
      (r=7 ∧ s=4 ∧ t=4 ∧ K=18 ∧ L=13) ∨
      (r=5 ∧ s=5 ∧ t=4 ∧ K=22 ∧ L=16) ∨
      (r=6 ∧ s=5 ∧ t=4 ∧ K=23 ∧ L=18) ∨
      (r=6 ∧ s=6 ∧ t=4 ∧ K=26 ∧ L=22) ∨
      (r=5 ∧ s=5 ∧ t=5 ∧ K=27 ∧ L=22)) :
    K ≤ max (A*B*C-1) L+ferrersPlaneDefect r A B+
      ferrersPlaneDefect s A C+ferrersPlaneDefect t B C := by
  have h12 := ferrersPlaneDefect_pressure_lower r A B (by omega) ha hb
  have h13 := ferrersPlaneDefect_pressure_lower s A C (by omega) ha hc
  have h23 := ferrersPlaneDefect_pressure_lower t B C (by omega) hb hc
  rcases hq with ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩
  all_goals
    by_cases hlarge : 7 ≤ A ∨ 7 ≤ B ∨ 7 ≤ C
    · exact bw_large_coordinate_pressure _ _ _ _ _ A B C (by omega) (by omega)
        (by omega) ha hb hc (by omega) hlarge
    · have ha6 : A ≤ 6 := by omega
      have hb6 : B ≤ 6 := by omega
      have hc6 : C ≤ 6 := by omega
      have hunit : (if B=1 ∧ C=1 then 4 else 0) ≤ ferrersPlaneDefect 4 B C := by
        split_ifs with h
        · rcases h with ⟨rfl,rfl⟩; decide
        · exact Nat.zero_le _
      interval_cases A <;> interval_cases B <;> interval_cases C <;>
        first | omega | (norm_num only [ite_true,ite_false,and_true,and_false,
          true_and,false_and] at h12 h13 h23 hunit; omega)

/-- Arbitrary actual minimal complement in the six exceptional small profiles. -/
theorem fullSupport_smallwidth_six_BW_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hq : (pair12Count S.D=6 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=7 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=6 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=5)) :
    fullTarget S ≤ fullSupportSymbolicBW S g := by
  have hb := fullSupport_symbolic_BW_core_box_lower S hg hf ho
  rw [fullCore_card_eq_coreCardRows] at hb
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  rcases hq with ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩ |
    ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩
  · have hp := six_pressure 6 4 4 18 13 g.x g.y g.z hf.1 hf.2.1 hf.2.2 (by omega) (by norm_num)
    have he : coreCardRows 6 4 4=14 := by decide
    rw [hr,hs,ht] at hb
    norm_num [he,largeHoleCap,Nat.choose] at hb
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num
    omega
  · have hp := six_pressure 7 4 4 18 13 g.x g.y g.z hf.1 hf.2.1 hf.2.2 (by omega) (by norm_num)
    have he : coreCardRows 7 4 4=14 := by decide
    rw [hr,hs,ht] at hb
    norm_num [he,largeHoleCap,Nat.choose] at hb
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num
    omega
  · have hp := six_pressure 5 5 4 22 16 g.x g.y g.z hf.1 hf.2.1 hf.2.2 (by omega) (by norm_num)
    have he : coreCardRows 5 5 4=17 := by decide
    rw [hr,hs,ht] at hb
    norm_num [he,largeHoleCap,Nat.choose] at hb
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num
    omega
  · have hp := six_pressure 6 5 4 23 18 g.x g.y g.z hf.1 hf.2.1 hf.2.2 (by omega) (by norm_num)
    have he : coreCardRows 6 5 4=19 := by decide
    rw [hr,hs,ht] at hb
    norm_num [he,largeHoleCap,Nat.choose] at hb
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num
    omega
  · have hp := six_pressure 6 6 4 26 22 g.x g.y g.z hf.1 hf.2.1 hf.2.2 (by omega) (by norm_num)
    have he : coreCardRows 6 6 4=23 := by decide
    rw [hr,hs,ht] at hb
    norm_num [he,largeHoleCap,Nat.choose] at hb
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num
    omega
  · have hp := six_pressure 5 5 5 27 22 g.x g.y g.z hf.1 hf.2.1 hf.2.2 (by omega) (by norm_num)
    have he : coreCardRows 5 5 5=23 := by decide
    rw [hr,hs,ht] at hb
    norm_num [he,largeHoleCap,Nat.choose] at hb
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num
    omega

end NSP3
