import NSP3.SharpnessAssembly

namespace NSP3.V03

open NSP3.Sharpness

/-- A finite cover of the canonical border bounds the intrinsic presentation invariant. -/
theorem intrinsicRho_le_border_cover (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (B : Finset Point3)
    (hcover : ∀ p, MinimalComplement (aperyStandardSet m a b c h.positive h.coprime) p →
      p ∈ B) : intrinsicRho (generatedSemigroup m a b c) ≤ B.card := by
  classical
  have hi : Function.Injective
      (fun p : PresentationBorder m a b c h.positive h.coprime =>
        (⟨p.1, hcover p.1 p.2⟩ : {q : Point3 // q ∈ B})) := by
    intro p q he
    have hv : p.1=q.1 := congrArg (fun u : {r : Point3 // r ∈ B} => u.1) he
    exact Subtype.ext hv
  have hc := Nat.card_le_card_of_injective _ hi
  have hc' : Nat.card (PresentationBorder m a b c h.positive h.coprime) ≤ B.card := by
    simpa using hc
  rw [literature_rho_identification m a b c h]
  exact (minimal_presentation_boundary_card_bridge m a b c h.positive h.coprime).trans hc'

/-- Exhaustion of the minimal complement of the even construction's exponent region. -/
theorem even_region_border_cover (L k : ℕ) (hk : 1 ≤ k) (hL : k < L)
    (p : Point3) (hout : ¬ EvenRegion L k p)
    (hx : 0 < p.x → EvenRegion L k p.pred1)
    (hy : 0 < p.y → EvenRegion L k p.pred2)
    (hz : 0 < p.z → EvenRegion L k p.pred3) : p ∈ evenBorder L k := by
  apply (evenBorder_mem L k p).mpr
  by_cases hpx : p.x = 0
  · by_cases hpz : p.z = 0
    · have hpy : 0 < p.y := by simp [EvenRegion, hpx, hpz] at hout; omega
      have hp := hy hpy
      have he : p.y = k+1 := by
        simp [EvenRegion, Point3.pred2, hpx, hpz] at hp hout
        omega
      right; right; left
      refine ⟨0, by omega, ?_⟩
      apply Point3.ext <;> simp_all
    · have hp := hz (by omega)
      have hs : p.y+p.z=k+1 := by
        simp [EvenRegion, Point3.pred3, hpx] at hp hout
        omega
      right; right; right
      refine ⟨p.z, by omega, by omega, ?_⟩
      apply Point3.ext <;> dsimp <;> omega
  · by_cases hpz : p.z = 0
    · have hp := hx (by omega)
      by_cases hpy : p.y = 0
      · have he : p.x=L := by
          simp [EvenRegion, Point3.pred1, hpy, hpz] at hp hout
          omega
        right; left
        apply Point3.ext <;> simp_all
      · have hs : p.x+p.y=k+1 := by
          simp [EvenRegion, Point3.pred1, hpz] at hp hout
          omega
        right; right; left
        refine ⟨p.x, by omega, ?_⟩
        apply Point3.ext <;> dsimp <;> omega
    · have hp₁ := hx (by omega)
      have hp₃ := hz (by omega)
      have he₁ : p.x=1 := by
        simp [EvenRegion, Point3.pred1] at hp₁
        omega
      have he₃ : p.z=1 := by
        simp [EvenRegion, Point3.pred3] at hp₃
        omega
      have he₂ : p.y=0 := by
        by_contra he
        have hp₂ := hy (by omega)
        simp [EvenRegion, Point3.pred2, he₁, he₃] at hp₂
      left
      apply Point3.ext <;> simp_all

/-- Exhaustion of the minimal complement of the odd construction's exponent region. -/
theorem odd_region_border_cover (L k : ℕ) (hk : 2 ≤ k) (hL : k ≤ L)
    (p : Point3) (hout : ¬ OddRegion L k p)
    (hx : 0 < p.x → OddRegion L k p.pred1)
    (hy : 0 < p.y → OddRegion L k p.pred2)
    (hz : 0 < p.z → OddRegion L k p.pred3) : p ∈ oddBorder L k := by
  apply (oddBorder_mem L k p).mpr
  by_cases hpx : p.x = 0
  · by_cases hpz : p.z = 0
    · have hpy : 0 < p.y := by simp [OddRegion, hpx, hpz] at hout; omega
      have hp := hy hpy
      have he : p.y=k+1 := by
        simp [OddRegion, Point3.pred2, hpx, hpz] at hp hout
        omega
      right; right; left
      apply Point3.ext <;> simp_all
    · have hp := hz (by omega)
      have hs : p.y+p.z=k := by
        by_cases hpy : p.y=0
        · simp [OddRegion, Point3.pred3, hpx, hpy] at hp hout
          omega
        · have hp₂ := hy (by omega)
          simp [OddRegion, Point3.pred2, hpx] at hp₂
          simp [OddRegion, hpx] at hout
          omega
      right; right; right; right
      refine ⟨p.z, by omega, by omega, ?_⟩
      apply Point3.ext <;> dsimp <;> omega
  · by_cases hpz : p.z = 0
    · have hp := hx (by omega)
      by_cases hpy : p.y = 0
      · have he : p.x=L+1 := by
          simp [OddRegion, Point3.pred1, hpy, hpz] at hp hout
          omega
        right; left
        apply Point3.ext <;> simp_all
      · have hs : p.x+p.y=k+1 := by
          simp [OddRegion, Point3.pred1, hpz] at hp hout
          omega
        right; right; right; left
        refine ⟨p.x, by omega, by omega, ?_⟩
        apply Point3.ext <;> dsimp <;> omega
    · have hp₁ := hx (by omega)
      have hp₃ := hz (by omega)
      have he₁ : p.x=1 := by
        simp [OddRegion, Point3.pred1] at hp₁
        omega
      have he₃ : p.z=1 := by
        simp [OddRegion, Point3.pred3] at hp₃
        omega
      have he₂ : p.y=0 := by
        by_contra he
        have hp₂ := hy (by omega)
        simp [OddRegion, Point3.pred2, he₁, he₃] at hp₂
      left
      apply Point3.ext <;> simp_all

theorem even_family_rho_eq (m k : ℕ) (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) :
    intrinsicRho (generatedSemigroup m (evenA m k) (evenB m k) (evenC m k)) =
      2*k+4 := by
  let L := m-k*k-k
  have ht : k*k+2*k+1 ≤ m := by nlinarith
  have hL : k < L := by dsimp [L]; omega
  have hrel : L+k*k+k=m := by dsimp [L]; omega
  have ha : evenA m k+1=(k+1)*m := by
    have : 0 < (k+1)*m := Nat.mul_pos (by omega) (by nlinarith)
    unfold evenA; omega
  have h := even_minimalFour m k hk hm
  have hmem : ∀ p, p ∈ aperyStandardSet m (evenA m k) (evenB m k) (evenC m k)
      h.positive h.coprime ↔ EvenRegion L k p := by
    intro p
    exact (mem_aperyStandardSet _ _ _ _ _ _ p).trans
      (even_canonical_iff m k L _ _ _ (by omega) hL hrel ha rfl rfl h.coprime p)
  apply le_antisymm ?_ (even_family_rho_lower m k hk hm)
  calc
    _ ≤ (evenBorder L k).card := intrinsicRho_le_border_cover _ _ _ _ h _ (by
      intro p hp
      exact even_region_border_cover L k hk hL p
        (fun hr => hp.not_mem ((hmem p).mpr hr))
        (fun hx => (hmem p.pred1).mp (hp.pred1_mem hx))
        (fun hy => (hmem p.pred2).mp (hp.pred2_mem hy))
        (fun hz => (hmem p.pred3).mp (hp.pred3_mem hz)))
    _ = 2*k+4 := evenBorder_card L k hk hL

theorem odd_family_rho_eq (m k : ℕ) (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) :
    intrinsicRho (generatedSemigroup m (oddA m k) (oddB m k) (oddC m k)) =
      2*k+3 := by
  let L := m-k*k-1
  have hL : k ≤ L := by dsimp [L]; omega
  have hrel : L+k*k+1=m := by dsimp [L]; omega
  have ha : oddA m k+1=k*m := by
    have : 0 < k*m := Nat.mul_pos (by omega) (by nlinarith)
    unfold oddA; omega
  have h := odd_minimalFour m k hk hm
  have hmem : ∀ p, p ∈ aperyStandardSet m (oddA m k) (oddB m k) (oddC m k)
      h.positive h.coprime ↔ OddRegion L k p := by
    intro p
    exact (mem_aperyStandardSet _ _ _ _ _ _ p).trans
      (odd_canonical_iff m k L _ _ _ hk hL hrel ha rfl rfl h.coprime p)
  apply le_antisymm ?_ (odd_family_rho_lower m k hk hm)
  calc
    _ ≤ (oddBorder L k).card := intrinsicRho_le_border_cover _ _ _ _ h _ (by
      intro p hp
      exact odd_region_border_cover L k hk hL p
        (fun hr => hp.not_mem ((hmem p).mpr hr))
        (fun hx => (hmem p.pred1).mp (hp.pred1_mem hx))
        (fun hy => (hmem p.pred2).mp (hp.pred2_mem hy))
        (fun hz => (hmem p.pred3).mp (hp.pred3_mem hz)))
    _ = 2*k+3 := oddBorder_card L k hk hL

end NSP3.V03
