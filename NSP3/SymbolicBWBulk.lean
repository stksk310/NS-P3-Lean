import NSP3.SymbolicBWRows
import NSP3.SymbolicSmallwidthQ544

namespace NSP3

private theorem choose_two_int (n : ℕ) :
    2*(Nat.choose n 2 : ℤ)+(n : ℤ)=(n : ℤ)^2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have h : 2*Nat.choose (n+1) 2=(n+1)*((n+1)-1) := by
        rw [Nat.choose_two_right]
        exact Nat.mul_div_cancel' (n+1).two_dvd_mul_sub_one
      norm_num only [Nat.add_sub_cancel] at h
      zify at h
      push_cast at h ⊢
      nlinarith

private theorem bulk_t4 (r s K : ℕ) (hs : 4 ≤ s) (hr : s ≤ r)
    (hc : 6*s ≤ K+(if r=s then 14 else if r=s+1 then 12 else 11))
    (hne : ¬ ((s=4 ∧ r≤7) ∨ (s=5 ∧ r≤6) ∨ (s=6 ∧ r=6))) :
    (r+s+4+2)^2 ≤ 4*(1+3*r+Nat.choose r 2+Nat.choose s 2+6+K+3) := by
  have cr := choose_two_int r
  have cs := choose_two_int s
  by_cases h0 : r=s
  · have hs7 : 7 ≤ s := by omega
    have hcb : 6*s ≤ K+14 := by split_ifs at hc; omega
    subst r
    zify at hcb hs7 ⊢
    nlinarith only [hcb,hs7,cr,cs]
  by_cases h1 : r=s+1
  · have hs6 : 6 ≤ s := by omega
    have hcb : 6*s ≤ K+12 := by split_ifs at hc; omega
    have h1z : (r : ℤ)=(s : ℤ)+1 := by exact_mod_cast h1
    zify at hcb hs6 ⊢
    nlinarith only [hcb,hs6,h1z,cr,cs]
  have hcb : 6*s ≤ K+11 := by split_ifs at hc; omega
  by_cases hs5 : 5 ≤ s
  · have hd : (2 : ℤ) ≤ (r : ℤ)-s := by omega
    have hp : 0 ≤ ((r : ℤ)-s)*((r : ℤ)-s-2) :=
      mul_nonneg (by omega) (by omega)
    zify at hcb hs5 ⊢
    nlinarith only [hcb,hs5,hp,cr,cs]
  · have hs4 : s=4 := by omega
    have hr8 : 8 ≤ r := by omega
    have hp : 0 ≤ ((r : ℤ)-4-4)*((r : ℤ)-4+2) :=
      mul_nonneg (by omega) (by omega)
    subst s
    zify at hcb ⊢
    norm_num at cs
    nlinarith only [hcb,hp,cr,cs]

private theorem bulk_t5 (r s K : ℕ) (hs : 5 ≤ s) (hr : s ≤ r)
    (hc : 10*s ≤ K+28) (hc' : s+1 ≤ r → 10*s ≤ K+24)
    (hne : ¬ (s=5 ∧ r=5)) :
    (r+s+5+2)^2 ≤ 4*(1+3*r+Nat.choose r 2+Nat.choose s 2+10+K+3) := by
  have cr := choose_two_int r
  have cs := choose_two_int s
  by_cases he : r=s
  · have hs6 : 6 ≤ s := by omega
    subst r
    zify at hc hs6 ⊢
    nlinarith only [hc,hs6,cr,cs]
  · have hstrict : s+1 ≤ r := by omega
    have hc2 := hc' hstrict
    have hp := sq_nonneg ((r : ℤ)-s-2)
    zify at hc2 hs ⊢
    nlinarith only [hc2,hs,hp,cr,cs]

private theorem bulk_t6 (r s K : ℕ) (hs : 6 ≤ s)
    (hc : 15*s ≤ K+52) :
    (r+s+6+2)^2 ≤ 4*(1+3*r+Nat.choose r 2+Nat.choose s 2+15+K+3) := by
  have cr := choose_two_int r
  have cs := choose_two_int s
  have hp := sq_nonneg ((r : ℤ)-s-3)
  zify at hc hs ⊢
  nlinarith only [hc,hs,hp,cr,cs]

/-- Shared quadratic proof, valid for unbounded r and s. Only six unfrozen
small profiles remain after the accepted q444/q544 branches. -/
theorem smallwidth_core_bulk_square (r s t : ℕ) (hr : s ≤ r) (hs : t ≤ s)
    (ht : t=4 ∨ t=5 ∨ t=6)
    (hne : ¬ ((t=4 ∧ s=4 ∧ r≤7) ∨ (t=4 ∧ s=5 ∧ r≤6) ∨
      (t=4 ∧ s=6 ∧ r=6) ∨ (t=5 ∧ s=5 ∧ r=5))) :
    (r+s+t+2)^2 ≤ 4*(1+3*r+Nat.choose r 2+Nat.choose s 2+Nat.choose t 2+
      (coreCardRows r s t-largeHoleCap t)+3) := by
  rcases ht with rfl | rfl | rfl
  · have hc := coreCardRows_t4_card r s hs hr
    have hc' : 6*s ≤ (coreCardRows r s 4-1)+
        (if r=s then 14 else if r=s+1 then 12 else 11) := by
      split_ifs at hc ⊢ <;> omega
    convert bulk_t4 r s (coreCardRows r s 4-1) hs hr hc' (by omega) using 1;
      norm_num [largeHoleCap,Nat.choose]
  · have hc := coreCardRows_t5_lower r s hs hr
    have hc' : 10*s ≤ coreCardRows r s 5-1+28 := by omega
    have hstrict : s+1 ≤ r → 10*s ≤ coreCardRows r s 5-1+24 := by
      intro h
      have := coreCardRows_t5_strict_lower r s hs h
      omega
    convert bulk_t5 r s (coreCardRows r s 5-1) hs hr hc' hstrict (by omega) using 1;
      norm_num [largeHoleCap,Nat.choose]
  · have hc := coreCardRows_t6_lower r s hs hr
    have hc' : 15*s ≤ coreCardRows r s 6-4+52 := by omega
    convert bulk_t6 r s (coreCardRows r s 6-4) hs hc' using 1;
      norm_num [largeHoleCap,Nat.choose]

theorem fullSupport_smallwidth_core_bulk_BW_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=4 ∨ pair23Count S.D=5 ∨ pair23Count S.D=6)
    (hne : ¬ ((pair23Count S.D=4 ∧ pair13Count S.D=4 ∧ pair12Count S.D≤7) ∨
      (pair23Count S.D=4 ∧ pair13Count S.D=5 ∧ pair12Count S.D≤6) ∨
      (pair23Count S.D=4 ∧ pair13Count S.D=6 ∧ pair12Count S.D=6) ∨
      (pair23Count S.D=5 ∧ pair13Count S.D=5 ∧ pair12Count S.D=5))) :
    fullTarget S ≤ fullSupportSymbolicBW S g := by
  have h := fullSupport_symbolic_BW_core_box_lower S hg hf ho
  have h12 : 1 ≤ ferrersPlaneDefect (pair12Count S.D) g.x g.y := le_max_left _ _
  have h13 : 1 ≤ ferrersPlaneDefect (pair13Count S.D) g.x g.z := le_max_left _ _
  have h23 : 1 ≤ ferrersPlaneDefect (pair23Count S.D) g.y g.z := le_max_left _ _
  have hm := le_max_right (g.x*g.y*g.z-1)
    ((fullCoreFinset S).card-largeHoleCap (pair23Count S.D))
  have hb : 1+3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+Nat.choose (pair23Count S.D) 2+
      ((fullCoreFinset S).card-largeHoleCap (pair23Count S.D))+3 ≤
        fullSupportSymbolicBW S g := by omega
  rw [fullCore_card_eq_coreCardRows] at hb
  have hsq := smallwidth_core_bulk_square _ _ _ ho.2 ho.1 ht hne
  rw [fullTarget_eq_square]
  omega

/-- A six-profile cover is a disjunction, not a proof of any residual branch. -/
theorem fullSupport_tGE4_six_profile_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) :
    fullTarget S ≤ S.m ∨
      ((pair12Count S.D=6 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=7 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=6 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=6 ∧ pair13Count S.D=6 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=5)) := by
  rcases fullSupport_smallwidth_refined_cover S hg hf ho ht with h | h
  · exact Or.inl h
  by_cases he : (pair23Count S.D=4 ∧ pair13Count S.D=4 ∧ pair12Count S.D≤7) ∨
      (pair23Count S.D=4 ∧ pair13Count S.D=5 ∧ pair12Count S.D≤6) ∨
      (pair23Count S.D=4 ∧ pair13Count S.D=6 ∧ pair12Count S.D=6) ∨
      (pair23Count S.D=5 ∧ pair13Count S.D=5 ∧ pair12Count S.D=5)
  · right
    have hs := ho.1
    have hr := ho.2
    omega
  · exact Or.inl (le_trans (fullSupport_smallwidth_core_bulk_BW_sharp S hg hf ho
      (by rcases h.2.2.1 with h | h | h <;> omega) he)
      (fullSupport_symbolic_BW_lower S hg hf ho))

end NSP3
