import P3TorSpike.TorBettiBounds

noncomputable section
namespace NSP3.TorSpike
open NSP3.V03

/-- Degree-two total Betti values of the actual numerical-semigroup class at multiplicity m. -/
def torBetti2Values (k : Type) [Field k] (m : ℕ) : Set ℕ :=
  {r | ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c, torBetti k m a b c 2 = r}

/-- Degree-three total Betti values of the actual numerical-semigroup class at multiplicity m. -/
def torBetti3Values (k : Type) [Field k] (m : ℕ) : Set ℕ :=
  {r | ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c, torBetti k m a b c 3 = r}

theorem torBetti2_values_upper (k : Type) [Field k] {m r : ℕ}
    (hr : r ∈ torBetti2Values k m) : r ≤ 2 * T m - 2 := by
  obtain ⟨a, b, c, h, rfl⟩ := hr
  exact (torBetti_simultaneous_bounds k m a b c h).2.1

theorem torBetti2_values_bddAbove (k : Type) [Field k] (m : ℕ) :
    BddAbove (torBetti2Values k m) :=
  ⟨2 * T m - 2, fun _ hr => torBetti2_values_upper k hr⟩

theorem torBetti2_values_finite (k : Type) [Field k] (m : ℕ) :
    (torBetti2Values k m).Finite :=
  (Set.finite_Iic (2 * T m - 2)).subset (fun _ hr => torBetti2_values_upper k hr)

/-- The known family at q=T supplies the lower endpoint as an actual Betti value. -/
theorem torBetti2_lower_value_mem (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    2 * T m - 4 ∈ torBetti2Values k m := by
  obtain ⟨a, b, c, h, _, _, h₂, _⟩ :=
    torBetti_family_realized k m (T m) (T_ge_six m hm) (T_square_bound m)
  exact ⟨a, b, c, h, h₂⟩

theorem torBetti2_values_nonempty (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    (torBetti2Values k m).Nonempty := ⟨_, torBetti2_lower_value_mem k m hm⟩

noncomputable def maximumTorBetti2 (k : Type) [Field k] (m : ℕ) : ℕ :=
  sSup (torBetti2Values k m)

/-- The degree-two maximum is attained on the actual class. -/
theorem maximumTorBetti2_isGreatest (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (torBetti2Values k m) (maximumTorBetti2 k m) := by
  exact ⟨(torBetti2_values_nonempty k m hm).csSup_mem (torBetti2_values_finite k m),
    fun _ hr => le_csSup (torBetti2_values_bddAbove k m) hr⟩

theorem maximumTorBetti2_attained (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c,
      torBetti k m a b c 2 = maximumTorBetti2 k m :=
  (maximumTorBetti2_isGreatest k m hm).1

/-- An attained window for the actual second total Betti maximum; no exact classification is claimed. -/
theorem maximumTorBetti2_window (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    2 * T m - 4 ≤ maximumTorBetti2 k m ∧ maximumTorBetti2 k m ≤ 2 * T m - 2 := by
  have hg := maximumTorBetti2_isGreatest k m hm
  exact ⟨hg.2 (torBetti2_lower_value_mem k m hm), torBetti2_values_upper k hg.1⟩

/-- Actual third Betti values agree with intrinsic PF-type values on the full numerical class. -/
theorem torBetti3Values_eq_typeValues (k : Type) [Field k] (m : ℕ) :
    torBetti3Values k m = typeValues m := by
  ext r
  constructor
  · rintro ⟨a, b, c, h, hr⟩
    have hs := minimal_generator_class_bridge m a b c h
    refine ⟨generatedAddSubmonoid m a b c, hs.2.2.2, hs.2.2.1, hs.1, ?_⟩
    change semigroupType (generatedSemigroup m a b c) = r
    rw [semigroupType_generated, ← torBetti_three k m a b c h]
    exact hr
  · rintro ⟨S, hcof, hedim, hmult, hr⟩
    obtain ⟨a, b, c, h, heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hmult
    have hset : generatedSemigroup m a b c = (S : Set ℕ) :=
      congrArg (fun U : AddSubmonoid ℕ => (U : Set ℕ)) heq
    refine ⟨a, b, c, h, ?_⟩
    rw [torBetti_three k m a b c h, ← semigroupType_generated, hset]
    exact hr

theorem torBetti3_values_finite (k : Type) [Field k] (m : ℕ) :
    (torBetti3Values k m).Finite := by
  rw [torBetti3Values_eq_typeValues]
  exact type_values_finite m

theorem torBetti3_values_nonempty (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    (torBetti3Values k m).Nonempty := by
  rw [torBetti3Values_eq_typeValues]
  exact ⟨_, lower_type_value_mem m hm⟩

noncomputable def maximumTorBetti3 (k : Type) [Field k] (m : ℕ) : ℕ :=
  sSup (torBetti3Values k m)

/-- The maximum of actual third Betti values is exactly the existing actual type maximum. -/
theorem maximumTorBetti3_eq_maximumType (k : Type) [Field k] (m : ℕ) :
    maximumTorBetti3 k m = maximumType m := by
  unfold maximumTorBetti3 maximumType
  rw [torBetti3Values_eq_typeValues]

theorem maximumTorBetti3_isGreatest (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (torBetti3Values k m) (maximumTorBetti3 k m) := by
  rw [torBetti3Values_eq_typeValues, maximumTorBetti3_eq_maximumType]
  exact maximumType_isGreatest m hm

theorem maximumTorBetti3_attained (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c,
      torBetti k m a b c 3 = maximumTorBetti3 k m :=
  (maximumTorBetti3_isGreatest k m hm).1

/-- The attained degree-three window is transported from the full intrinsic PF-type class. -/
theorem maximumTorBetti3_window (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    T m - 3 ≤ maximumTorBetti3 k m ∧ maximumTorBetti3 k m ≤ T m - 1 := by
  rw [maximumTorBetti3_eq_maximumType]
  exact maximumType_window m hm

#print axioms maximumTorBetti2_attained
#print axioms maximumTorBetti2_window
#print axioms torBetti3Values_eq_typeValues
#print axioms maximumTorBetti3_eq_maximumType
#print axioms maximumTorBetti3_attained
#print axioms maximumTorBetti3_window

end NSP3.TorSpike
