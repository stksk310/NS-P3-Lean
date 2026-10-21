import NSP3.SymbolicThin23Resources
import NSP3.FullTarget

namespace NSP3

/-- Infinite arithmetic comparison; the balanced family r = s = h is excluded. -/
theorem thin23_nonbalanced_arithmetic (r s h : ℕ) (hs : 2 ≤ s)
    (hrs : s ≤ r) (hrh : r ≤ h) (hne : s < r ∨ r < h) :
    ((r+s+4)^2+3)/4 ≤ Nat.choose r 2+Nat.choose s 2+4*h+r+3 := by
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r := by omega
  have es : s-1+1=s := by omega
  have hn : (r+s+4)^2 ≤ 4*(Nat.choose r 2+Nat.choose s 2+4*h+r+3) := by
    have hd : 0 ≤ (r-s)^2 := Nat.zero_le _
    have he : r-s+s=r := Nat.sub_add_cancel hrs
    rcases hne with hdpos | hepos
    · have hd1 : 1 ≤ r-s := by omega
      nlinarith
    · nlinarith
  omega

/-- All nonbalanced t2/h11 parameters, without an upper bound on counts. -/
theorem fullSupport_t2_h11_nonbalanced_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1)
    (hne : pair13Count S.D < pair12Count S.D ∨ pair12Count S.D < g.x) :
    fullTarget S ≤ S.m := by
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  have hh : pair12Count S.D ≤ g.x := by omega
  have ha := thin23_nonbalanced_arithmetic (pair12Count S.D) (pair13Count S.D)
    g.x hs ho.2 hh hne
  have hb := fullSupport_t2_h11_lower S hg hf ho ht hs hy hz
  rw [fullTarget_eq_square,ht]
  simpa only [Nat.add_assoc] using le_trans ha hb

end NSP3
