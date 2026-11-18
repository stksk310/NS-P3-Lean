import NSP3.MacaulayC3

namespace NSP3.V03

/-- V03's short binomial comparison, without a fourth-degree expansion. -/
theorem sqrt_lt_binomial (r m : ℕ) (hr : 4 ≤ r)
    (hm : m < (r+3).choose 3) :
    2 + Nat.sqrt (4*m) < (r+2).choose 2 := by
  let B := (r+2).choose 2
  let U := (r+3).choose 3
  have hb : 2*B=(r+2)*(r+1) := c3_choose_two_poly r
  have hu : 3*U=(r+3)*B := by
    have h := c3_choose_three_poly r
    change 6*U=(r+3)*(r+2)*(r+1) at h
    nlinarith only [hb,h]
  have hb2 : 2 ≤ B := by nlinarith only [hb,hr]
  have hgap : 4*r+24 < 3*B := by
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hr
    nlinarith only [hb, Nat.zero_le (t*t), Nat.zero_le t]
  have he : B-2+2=B := Nat.sub_add_cancel hb2
  have hpos : 0 < B*(3*B-(4*r+24)) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hgap)
  have hsub : 3*B-(4*r+24)+(4*r+24)=3*B :=
    Nat.sub_add_cancel (by omega)
  have hsq : 4*m < (B-2)^2 := by
    change m < U at hm
    nlinarith only [hu,he,hpos,hsub,hm]
  have hs := Nat.sqrt_lt'.mpr hsq
  omega

theorem macaulay_small (m : ℕ) (hm : 4 ≤ m) (hu : m ≤ 9) :
    2 + Nat.sqrt (4*m) = C3 m := by
  interval_cases m <;> norm_num <;> decide

theorem macaulay_middle (m : ℕ) (hm : 10 ≤ m) (hu : m ≤ 19) :
    2 + Nat.sqrt (4*m) < C3 m := by
  interval_cases m <;> norm_num <;> decide

theorem macaulay_large (m : ℕ) (hm : 20 ≤ m) :
    2 + Nat.sqrt (4*m) < C3 m :=
  lt_of_lt_of_le
    (sqrt_lt_binomial (c3Degree m) m (c3Degree_ge_four m hm)
      (c3Degree_interval m (by omega)).2)
    (C3_ge_binomial m (by omega))

theorem macaulay_strict (m : ℕ) (hm : 10 ≤ m) :
    2 + Nat.sqrt (4*m) < C3 m := by
  by_cases hu : m ≤ 19
  · exact macaulay_middle m hm hu
  · exact macaulay_large m (by omega)

theorem macaulay_equality_iff (m : ℕ) (hm : 4 ≤ m) :
    2 + Nat.sqrt (4*m) = C3 m ↔ m ≤ 9 := by
  constructor
  · intro he
    by_contra hn
    have hlt := macaulay_strict m (by omega)
    omega
  · exact macaulay_small m hm

end NSP3.V03
