import NSP3.SymbolicBWCore

namespace NSP3
open Finset

/-- The left endpoint contributes AB, including the boundary A+B=r. -/
theorem ferrersW_endpoint_lower (r A B : ℕ) (h : A+B ≤ r) :
    A*B ≤ ferrersW r A B := by
  have hm : A ∈ Icc A (r-B) := mem_Icc.mpr ⟨le_rfl,by omega⟩
  have hs := single_le_sum (f := fun i => min (A*(r-i)) (B*i))
    (fun _ _ => Nat.zero_le _) hm
  have hmul := Nat.mul_le_mul_left A (show B ≤ r-A by omega)
  have hmin : A*B ≤ min (A*(r-A)) (B*A) := le_min hmul (le_of_eq (Nat.mul_comm A B))
  exact le_trans hmin hs

/-- Every summand contributes AB; count the exact closed interval. -/
theorem ferrersW_interval_product_lower (r A B : ℕ) (h : A+B ≤ r) :
    (r-B+1-A)*(A*B) ≤ ferrersW r A B := by
  have hs : (Icc A (r-B)).sum (fun _ => A*B) ≤ ferrersW r A B := by
    apply sum_le_sum
    intro i hi
    have hi' := mem_Icc.mp hi
    apply le_min
    · exact Nat.mul_le_mul_left A (by omega)
    · simpa [Nat.mul_comm] using Nat.mul_le_mul_left B hi'.1
  simpa [sum_const,Nat.card_Icc,nsmul_eq_mul] using hs

/-- A diagonal path of length A+B-r injects into the upper-right rectangle.
No coordinate ceiling or symmetry/monotonicity of W is used. -/
theorem ferrersRectangle_diagonal_lower (r A B : ℕ)
    (hr : 1 ≤ r) (ha : 1 ≤ A) (hb : 1 ≤ B) :
    A+B-r ≤ (ferrersRectangle r A B).card := by
  let f : ℕ → ℕ × ℕ := fun i =>
    (min A (r+i-1),r+i-min A (r+i-1))
  have hxy (i : ℕ) : (f i).1+(f i).2=r+i := by
    dsimp [f]
    have hmin := min_le_right A (r+i-1)
    omega
  have hsub : (Icc 1 (A+B-r)).image f ⊆ ferrersRectangle r A B := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    have hi' := mem_Icc.mp hi
    have he := hxy i
    have hx : 1 ≤ (f i).1 ∧ (f i).1 ≤ A := by dsimp [f]; omega
    have hy : 1 ≤ (f i).2 ∧ (f i).2 ≤ B := by dsimp [f]; omega
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr hx,mem_Icc.mpr hy⟩,by omega⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have he := congrArg (fun p : ℕ × ℕ => p.1+p.2) hij
    rw [hxy,hxy] at he
    omega
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hinj] at hc
  simpa [Nat.card_Icc] using hc

/-- A conservative pressure function, not a monotonicity claim about D. -/
theorem ferrersPlaneDefect_pressure_lower (r A B : ℕ)
    (hr : 1 ≤ r) (ha : 1 ≤ A) (hb : 1 ≤ B) :
    max 1 (if A+B ≤ r then (r-B+1-A)*(A*B) else A+B-r) ≤
      ferrersPlaneDefect r A B := by
  apply max_le (le_max_left _ _)
  split_ifs with h
  · exact le_trans (ferrersW_interval_product_lower r A B h)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact le_trans (ferrersRectangle_diagonal_lower r A B hr ha hb)
      (le_trans (le_max_left _ _) (le_max_right _ _))

end NSP3
