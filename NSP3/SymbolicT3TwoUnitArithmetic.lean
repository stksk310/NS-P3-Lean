import NSP3.SymbolicT3TwoUnitBudget

namespace NSP3

theorem two_unit_square_gap_identity (r s w : ℤ) :
    2*r*(r-1)+2*s*(s-1)+20*r+12*s+4*w-20-(r+s+5)^2=
      (r-s)^2+8*r+4*w-45 := by ring

/-- A single polynomial comparison handles both orientations, including equality. -/
theorem two_unit_budget_square (r s w m : ℕ) (hs : 3 ≤ s) (hr : s ≤ r) (h4 : 4 ≤ r)
    (hw : 2 ≤ w) (hw4 : 4 ≤ s → 4 ≤ w)
    (hb : Nat.choose r 2+Nat.choose s 2+5*r+3*s+w ≤ m+5)
    (hb' : s<r → Nat.choose r 2+Nat.choose s 2+5*r+3*s+w ≤ m+4) :
    (r+s+5)^2 ≤ 4*m := by
  by_cases h5 : 5 ≤ r
  · have cr : 2*Nat.choose r 2=r*(r-1) := by
      rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
    have cs : 2*Nat.choose s 2=s*(s-1) := by
      rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
    have er : r-1+1=r := by omega
    have es : s-1+1=s := by omega
    have ed : r-s+s=r := Nat.sub_add_cancel hr
    have hgap : 45 ≤ (r-s)^2+8*r+4*w := by
      nlinarith only [h5,hw,Nat.zero_le ((r-s)^2)]
    nlinarith only [hb,cr,cs,er,es,ed,hgap]
  · have he : r=4 := by omega
    by_cases hs4 : 4 ≤ s
    · have he' : s=4 := by omega
      have hw' := hw4 hs4
      norm_num [he,he',Nat.choose] at hb ⊢
      omega
    · have he' : s=3 := by omega
      have hb'' := hb' (by omega)
      norm_num [he,he',Nat.choose] at hb'' ⊢
      omega

theorem t3_two_unit_BW_coarse (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      5*pair12Count S.D+3*pair13Count S.D+
      ferrersW (if g.y=1 then pair12Count S.D else pair13Count S.D) 1 1 ≤
        fullSupportSymbolicBW S g+5 := by
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hs : 3 ≤ pair13Count S.D := by have := ho.1;omega
  have hsr := ho.2
  have hL : pair13Count S.D-2 ≤ min (pair12Count S.D-2) (pair13Count S.D-1) := by omega
  by_cases hy : g.y=1
  · have he := t3_two_unit_11h_BW_exact S hg hf ho ht hx hy
    simp only [hy,ite_true]
    omega
  · have hz : g.z=1 := hu.resolve_left hy
    have he := t3_two_unit_1h1_BW_exact S hg hf ho ht hx hz
    simp only [hy,ite_false]
    omega

/-- The extra unit is essential for the misaligned r4/s3 equality case. -/
theorem t3_two_unit_BW_nonbalanced (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hu : g.y=1 ∨ g.z=1)
    (hn : pair13Count S.D<pair12Count S.D) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      5*pair12Count S.D+3*pair13Count S.D+
      ferrersW (if g.y=1 then pair12Count S.D else pair13Count S.D) 1 1 ≤
        fullSupportSymbolicBW S g+4 := by
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hs : 3 ≤ pair13Count S.D := by have := ho.1;omega
  have hL : pair13Count S.D-1 ≤ min (pair12Count S.D-2) (pair13Count S.D-1) := by omega
  by_cases hy : g.y=1
  · have he := t3_two_unit_11h_BW_exact S hg hf ho ht hx hy
    simp only [hy,ite_true]
    omega
  · have hz : g.z=1 := hu.resolve_left hy
    have he := t3_two_unit_1h1_BW_exact S hg hf ho ht hx hz
    simp only [hy,ite_false]
    omega

/-- Infinite BW coverage leaves precisely the two q333/height3 endpoints. -/
theorem fullSupport_t3_two_unit_BW_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) :
    fullTarget S ≤ S.m ∨ (pair12Count S.D=3 ∧ pair13Count S.D=3 ∧
      ((g.y=3 ∧ g.z=1) ∨ (g.y=1 ∧ g.z=3))) := by
  have hb := fullSupport_symbolic_BW_lower S hg hf ho
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hs : 3 ≤ pair13Count S.D := by have := ho.1;omega
  have hsr := ho.2
  by_cases h4 : 4 ≤ pair12Count S.D
  · left
    let r := pair12Count S.D
    let s := pair13Count S.D
    let u := if g.y=1 then r else s
    have hu3 : 3 ≤ u := by dsimp [u,r,s];split <;> omega
    have hu4 : 4 ≤ s → 4 ≤ u := by dsimp [u,r,s];split <;> omega
    have hw := two_unit_W_ge_two u hu3
    have hw4 : 4 ≤ s → 4 ≤ ferrersW u 1 1 :=
      fun h=>two_unit_W_ge_four u (hu4 h)
    have hm := t3_two_unit_BW_coarse S hg hf ho ht hx hu
    have hm' : s<r → Nat.choose r 2+Nat.choose s 2+5*r+3*s+ferrersW u 1 1 ≤ S.m+4 := by
      intro hn
      have hh := t3_two_unit_BW_nonbalanced S hg hf ho ht hx hu hn
      change Nat.choose r 2+Nat.choose s 2+5*r+3*s+ferrersW u 1 1 ≤ _ at hh
      omega
    change Nat.choose r 2+Nat.choose s 2+5*r+3*s+ferrersW u 1 1 ≤ _ at hm
    have hsq := two_unit_budget_square r s (ferrersW u 1 1) S.m hs hsr h4 hw hw4 (by omega) hm'
    rw [fullTarget_eq_square,ht]
    change ((r+s+3+2)^2+3)/4 ≤ S.m
    have he : r+s+3+2=r+s+5 := by omega
    rw [he];omega
  · have hr : pair12Count S.D=3 := by omega
    have hs' : pair13Count S.D=3 := by omega
    have htar : fullTarget S=31 := by rw [fullTarget_eq_square,hr,hs',ht];norm_num
    rcases hu with hy | hz
    · have he := t3_two_unit_11h_BW_exact S hg hf ho ht hx hy
      rw [hr,hs'] at he
      have hw : ferrersW 3 1 1=2 := by decide
      norm_num [hw,Nat.choose] at he
      by_cases hheight : 4 ≤ g.z
      · left;rw [htar];omega
      · right;exact ⟨hr,hs',Or.inr ⟨hy,by omega⟩⟩
    · have he := t3_two_unit_1h1_BW_exact S hg hf ho ht hx hz
      rw [hr,hs'] at he
      have hw : ferrersW 3 1 1=2 := by decide
      norm_num [hw,Nat.choose] at he
      by_cases hheight : 4 ≤ g.y
      · left;rw [htar];omega
      · right;exact ⟨hr,hs',Or.inl ⟨by omega,hz⟩⟩

end NSP3
