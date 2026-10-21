import NSP3.AtomFactorization

namespace NSP3.CommonCard

abbrev FourCoeff := Fin 4 → ℕ

/-- The positive grading on the four free generators. -/
def degree (g : Fin 4 → ℕ) (u : FourCoeff) : ℕ := ∑ i, u i * g i

@[simp] theorem degree_zero (g : Fin 4 → ℕ) : degree g 0 = 0 := by
  simp [degree]

theorem degree_add (g : Fin 4 → ℕ) (u v : FourCoeff) :
    degree g (u + v) = degree g u + degree g v := by
  simp only [degree, Pi.add_apply, Nat.add_mul, Finset.sum_add_distrib]

/-- A coordinate is bounded by its total degree when all generators are positive. -/
theorem coordinate_le_degree (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (u : FourCoeff) (i : Fin 4) : u i ≤ degree g u := by
  calc
    u i = u i * 1 := (Nat.mul_one _).symm
    _ ≤ u i * g i := Nat.mul_le_mul_left _ (hg i)
    _ ≤ degree g u := Finset.single_le_sum (fun j _ => Nat.zero_le (u j * g j))
      (Finset.mem_univ i)

theorem degree_eq_zero_iff (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (u : FourCoeff) : degree g u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    funext i
    have hi := coordinate_le_degree g hg u i
    simpa [hu] using hi
  · rintro rfl
    exact degree_zero g

theorem degree_pos_iff (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (u : FourCoeff) : 0 < degree g u ↔ u ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, degree_eq_zero_iff g hg u]

/-- Finite fibers follow directly from positive generators, without a degree cap hypothesis. -/
theorem fiber_finite_positive (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i) (n : ℕ) :
    Finite {u : FourCoeff // degree g u = n} := by
  let f : {u : FourCoeff // degree g u = n} → (Fin 4 → Fin (n + 1)) :=
    fun u i => ⟨u.val i, Nat.lt_succ_of_le (by
      have hi := coordinate_le_degree g hg u.val i
      simpa [u.property] using hi)⟩
  apply Finite.of_injective f
  intro u v huv
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun huv i)

@[simp] theorem degree_single (g : Fin 4 → ℕ) (i : Fin 4) :
    degree g (Pi.single i 1) = g i := by
  classical
  simp [degree, Pi.single_apply]

/-- Removing a single positive coordinate uses guarded natural subtraction. -/
theorem subtract_single_reconstruct (u : FourCoeff) (i : Fin 4) (hi : 0 < u i) :
    u = (u - Pi.single i 1) + Pi.single i 1 := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
    omega
  · simp [Pi.single_apply, hj, Ne.symm hj]

/-- Every intrinsic support edge descends to an equal-degree pair of strictly lower degree. -/
theorem support_edge_strict_lower (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (u v : FourCoeff) (he : degree g u = degree g v)
    (hs : ∃ i, 0 < u i ∧ 0 < v i) :
    ∃ i u' v', u = u' + Pi.single i 1 ∧ v = v' + Pi.single i 1 ∧
      degree g u' = degree g v' ∧ degree g u' < degree g u := by
  classical
  obtain ⟨i, hui, hvi⟩ := hs
  let u' := u - Pi.single i 1
  let v' := v - Pi.single i 1
  have hu : u = u' + Pi.single i 1 := subtract_single_reconstruct u i hui
  have hv : v = v' + Pi.single i 1 := subtract_single_reconstruct v i hvi
  have hdu : degree g u = degree g u' + g i := by rw [hu, degree_add, degree_single]
  have hdv : degree g v = degree g v' + g i := by rw [hv, degree_add, degree_single]
  refine ⟨i, u', v', hu, hv, ?_, ?_⟩
  · omega
  · have hi := hg i
    omega

/-- A nonzero additive context supplies a common positive coordinate to its endpoints. -/
theorem context_common_support (u v d : FourCoeff) (hd : d ≠ 0) :
    ∃ i, 0 < (u + d) i ∧ 0 < (v + d) i := by
  have hdi : ∃ i, d i ≠ 0 := by
    by_contra h
    apply hd
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hdi
  refine ⟨i, ?_, ?_⟩ <;> simp only [Pi.add_apply] <;> omega

theorem context_degree_strict (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (u d : FourCoeff) (hd : d ≠ 0) : degree g u < degree g (u + d) := by
  have hp := (degree_pos_iff g hg d).mpr hd
  rw [degree_add]
  omega

/-- Compatibility with the frozen four-factorization grading. -/
theorem degree_fourCoordinates (m a b c : ℕ) (u : Fact4) :
    degree ![m,a,b,c] (fourCoordinates u) = factorWeight m a b c u := by
  simp only [degree, Fin.sum_univ_succ]
  change u.1*m + (u.2.x*a + (u.2.y*b + (u.2.z*c + 0))) = factorWeight m a b c u
  unfold factorWeight aperyWeight
  ring

theorem generators_positive (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    ∀ i : Fin 4, 0 < (![m,a,b,c] : Fin 4 → ℕ) i := by
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact h.positive
  · exact lt_of_lt_of_le h.positive h.least_a
  · exact lt_of_lt_of_le h.positive h.least_b
  · exact lt_of_lt_of_le h.positive h.least_c

end NSP3.CommonCard
