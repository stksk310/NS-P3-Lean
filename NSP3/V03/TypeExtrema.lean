import NSP3.V03.TypeBounds

namespace NSP3.V03

/-- Type values of actual cofinite embedding-dimension-four submonoids. -/
def typeValues (m : ℕ) : Set ℕ :=
  {r | ∃ S : AddSubmonoid ℕ, ((S : Set ℕ)ᶜ).Finite ∧
    semigroupEmbeddingDimension (S : Set ℕ)=4 ∧
    IsSemigroupMultiplicity (S : Set ℕ) m ∧ semigroupType (S : Set ℕ)=r}

theorem type_values_upper {m r : ℕ} (hr : r∈typeValues m) : r≤T m-1 := by
  obtain ⟨S,hcof,hedim,hmult,he⟩ := hr
  rw [← he]
  exact numerical_semigroup_type_upper S m hcof hedim hmult

theorem lower_type_value_mem (m : ℕ) (hm : 4 ≤ m) : T m-3∈typeValues m := by
  obtain ⟨a,b,c,h,_,htype⟩ := extremal_presentation_type_realized m hm
  have hs := minimal_generator_class_bridge m a b c h
  refine ⟨generatedAddSubmonoid m a b c,hs.2.2.2,hs.2.2.1,hs.1,?_⟩
  change semigroupType (generatedSemigroup m a b c)=T m-3
  rw [semigroupType_generated,htype]

theorem type_values_finite (m : ℕ) : (typeValues m).Finite :=
  (Set.finite_Iic (T m-1)).subset (fun _ hr => type_values_upper hr)

noncomputable def maximumType (m : ℕ) : ℕ := sSup (typeValues m)

theorem maximumType_isGreatest (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (typeValues m) (maximumType m) := by
  have hne : (typeValues m).Nonempty := ⟨_,lower_type_value_mem m hm⟩
  have hb : BddAbove (typeValues m) := ⟨T m-1,fun _ hr => type_values_upper hr⟩
  exact ⟨hne.csSup_mem (type_values_finite m),fun _ hr => le_csSup hb hr⟩

/-- V03's extremal type window, with an attained maximum on the actual class. -/
theorem maximumType_window (m : ℕ) (hm : 4 ≤ m) :
    T m-3 ≤ maximumType m ∧ maximumType m ≤ T m-1 := by
  have hg := maximumType_isGreatest m hm
  exact ⟨hg.2 (lower_type_value_mem m hm),type_values_upper hg.1⟩

end NSP3.V03
