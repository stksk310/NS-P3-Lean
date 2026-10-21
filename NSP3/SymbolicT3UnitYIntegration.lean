import NSP3.SymbolicT3UnitYSharp
import NSP3.SymbolicT3UnitIntegration

namespace NSP3

/-- A further infinite x-unit family closes by volume and the long-count gap. -/
theorem fullSupport_t3_unit_x_far_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z)
    (hfar : pair13Count S.D+2 ≤ pair12Count S.D) : fullTarget S ≤ S.m := by
  let r := pair12Count S.D
  let s := pair13Count S.D
  have hm := fullSupport_t3_positive_box_yz_lower S hg hf ho ht hy hz
  simp only [hx,one_mul] at hm
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  have hsum : r+1 ≤ g.y+g.z := by dsimp [r];omega
  have hv : 2*r ≤ g.y*g.z+2 := by
    have ey : g.y-2+2=g.y := by omega
    have ez : g.z-2+2=g.z := by omega
    have hn : 0 ≤ (g.y-2)*(g.z-2) := Nat.zero_le _
    nlinarith only [ey,ez,hn,hsum]
  have hbase : Nat.choose r 2+Nat.choose s 2+7*r ≤ S.m+2 := by
    change Nat.choose r 2+Nat.choose s 2+3*r+g.y*g.z+g.y*g.z+2 ≤ S.m at hm
    omega
  have hs : 3 ≤ s := by have := ho.1;dsimp [s];omega
  have hsr : s ≤ r := ho.2
  have hd : 2 ≤ r-s := by change s+2 ≤ r at hfar;omega
  have ed : r-s+s=r := Nat.sub_add_cancel hsr
  have hd2 : 4 ≤ (r-s)^2 := by nlinarith only [hd]
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r := by omega
  have es : s-1+1=s := by omega
  have hsq : (r+s+5)^2 ≤ 4*S.m := by
    nlinarith only [hbase,cr,cs,er,es,hs,ed,hd,hd2]
  rw [fullTarget_eq_square,ht]
  change ((r+s+3+2)^2+3)/4 ≤ S.m
  have he : r+s+3+2=r+s+5 := by omega
  rw [he];omega

/-- Ordered t3 is now completely sharp whenever the x coordinate is nonunit. -/
theorem fullSupport_t3_x_nonunit_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : 2 ≤ g.x) : fullTarget S ≤ S.m := by
  by_cases hz : g.z=1
  · exact fullSupport_t3_z_unit_or_h11_sharp S hg hf ho ht hx hz
  · have hz2 : 2 ≤ g.z := by have := hf.2.2;omega
    by_cases hy : g.y=1
    · exact fullSupport_t3_one_unit_y_symbolic_sharp S hg hf ho ht hy hx hz2
    · exact fullSupport_t3_nonunit_ordered_sharp S hg hf ho ht hx (by have := hf.2.1;omega) hz2

/-- Exact remaining scope, not the still-open universal ordered-t3 theorem. -/
theorem fullSupport_t3_remaining_x_unit_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) :
    fullTarget S ≤ S.m ∨
      (g.x=1 ∧ 2 ≤ g.y ∧ 2 ≤ g.z ∧ pair12Count S.D ≤ pair13Count S.D+1) ∨
      (g.x=1 ∧ 2 ≤ g.y ∧ g.z=1) ∨ (g.x=1 ∧ g.y=1 ∧ 2 ≤ g.z) := by
  by_cases hx : 2 ≤ g.x
  · exact Or.inl (fullSupport_t3_x_nonunit_symbolic_sharp S hg hf ho ht hx)
  have hx1 : g.x=1 := by have := hf.1;omega
  rcases fullSupport_t3_unit_partition S hg hf ho ht with
    hnon | hh11 | h1h1 | h11h | hxy1 | hx1z | h1yz
  · omega
  · omega
  · exact Or.inr (Or.inr (Or.inl h1h1))
  · exact Or.inr (Or.inr (Or.inr h11h))
  · omega
  · omega
  · by_cases hfar : pair13Count S.D+2 ≤ pair12Count S.D
    · exact Or.inl (fullSupport_t3_unit_x_far_sharp S hg hf ho ht h1yz.1 h1yz.2.1 h1yz.2.2 hfar)
    · exact Or.inr (Or.inl ⟨h1yz.1,h1yz.2.1,h1yz.2.2,by omega⟩)

end NSP3
