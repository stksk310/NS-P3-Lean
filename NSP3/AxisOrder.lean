import NSP3.PureIntercepts

namespace NSP3

private theorem axis_addOrder_lower
    (S : CyclicStaircase) (p : ZMod S.m) (a : ℕ)
    (hmem : ∀ k : Fin a, Point3.mk k.1 0 0 ∈ S.D)
    (hres : ∀ k : ℕ, S.residue (Point3.mk k 0 0) = k • p) :
    a ≤ addOrderOf p := by
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  by_contra hnot
  have hordlt : addOrderOf p < a := Nat.lt_of_not_ge hnot
  let k : Fin a := ⟨addOrderOf p, hordlt⟩
  have hk := hmem k
  have hz : Point3.zero ∈ S.D := by
    have ha : 0 < a := by
      have hp : 0 < addOrderOf p := (isOfFinAddOrder_of_finite p).addOrderOf_pos
      omega
    exact hmem ⟨0, ha⟩
  have heq := S.standard_eq_of_residue_eq hk hz
    (by rw [hres, addOrderOf_nsmul_eq_zero, S.residue_zero])
  have hv := congrArg Point3.x heq
  change addOrderOf p = 0 at hv
  exact (isOfFinAddOrder_of_finite p).addOrderOf_pos.ne' hv

/-- The first residue generator has additive order at least the number of
standard points on the first axis. -/
theorem axis1_addOrder_lower (S : CyclicStaircase) :
    pure1Intercept S ≤ addOrderOf S.p1 := by
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  apply axis_addOrder_lower S S.p1 (pure1Intercept S)
  · intro k
    exact (pure1_axis_mem_iff S k.1).mpr k.2
  · intro k
    simp [CyclicStaircase.residue, residueOf, nsmul_eq_mul]

/-- The second residue generator has additive order at least the number of
standard points on the second axis. -/
theorem axis2_addOrder_lower (S : CyclicStaircase) :
    pure2Intercept S ≤ addOrderOf S.p2 := by
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  by_contra hnot
  have hordlt : addOrderOf S.p2 < pure2Intercept S := Nat.lt_of_not_ge hnot
  have hk : Point3.mk 0 (addOrderOf S.p2) 0 ∈ S.D :=
    (pure2_axis_mem_iff S _).mpr hordlt
  have hz : Point3.zero ∈ S.D := by
    apply (pure2_axis_mem_iff S 0).mpr
    have hp := (isOfFinAddOrder_of_finite S.p2).addOrderOf_pos
    omega
  have hmul : (addOrderOf S.p2 : ZMod S.m) * S.p2 = 0 := by
    rw [← nsmul_eq_mul]
    exact addOrderOf_nsmul_eq_zero S.p2
  have heq := S.standard_eq_of_residue_eq hk hz (by
    simp [CyclicStaircase.residue, residueOf, hmul])
  have hv := congrArg Point3.y heq
  change addOrderOf S.p2 = 0 at hv
  exact (isOfFinAddOrder_of_finite S.p2).addOrderOf_pos.ne' hv

/-- The third residue generator has additive order at least the number of
standard points on the third axis. -/
theorem axis3_addOrder_lower (S : CyclicStaircase) :
    pure3Intercept S ≤ addOrderOf S.p3 := by
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  by_contra hnot
  have hordlt : addOrderOf S.p3 < pure3Intercept S := Nat.lt_of_not_ge hnot
  have hk : Point3.mk 0 0 (addOrderOf S.p3) ∈ S.D :=
    (pure3_axis_mem_iff S _).mpr hordlt
  have hz : Point3.zero ∈ S.D := by
    apply (pure3_axis_mem_iff S 0).mpr
    have hp := (isOfFinAddOrder_of_finite S.p3).addOrderOf_pos
    omega
  have hmul : (addOrderOf S.p3 : ZMod S.m) * S.p3 = 0 := by
    rw [← nsmul_eq_mul]
    exact addOrderOf_nsmul_eq_zero S.p3
  have heq := S.standard_eq_of_residue_eq hk hz (by
    simp [CyclicStaircase.residue, residueOf, hmul])
  have hv := congrArg Point3.z heq
  change addOrderOf S.p3 = 0 at hv
  exact (isOfFinAddOrder_of_finite S.p3).addOrderOf_pos.ne' hv

end NSP3
