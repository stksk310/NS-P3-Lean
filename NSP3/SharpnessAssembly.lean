import NSP3.SharpnessApery
import NSP3.SharpnessLowerBound
import NSP3.SharpnessBorders
import NSP3.SharpnessFamilies
import NSP3.SharpnessBorderWeights
import NSP3.SharpnessOddWeights
import NSP3.NumericalClassCoverage

namespace NSP3.Sharpness

open NSP3.CommonCard

def pointFour (p : Point3) : FourCoeff := ![0,p.x,p.y,p.z]

theorem pointFour_injective : Function.Injective pointFour := by
  intro p q he
  have hx := congrFun he (1 : Fin 4)
  have hy := congrFun he (2 : Fin 4)
  have hz := congrFun he (3 : Fin 4)
  apply Point3.ext
  · simpa [pointFour] using hx
  · simpa [pointFour] using hy
  · simpa [pointFour] using hz

theorem degree_four_parts (m a b c : ℕ) (u : FourCoeff) :
    degree ![m,a,b,c] u = u 0*m+aperyWeight a b c ⟨u 1,u 2,u 3⟩ := by
  simp only [degree,Fin.sum_univ_succ]
  simp [aperyWeight]
  ring

theorem degree_pointFour (m a b c : ℕ) (p : Point3) :
    degree ![m,a,b,c] (pointFour p) = aperyWeight a b c p := by
  rw [degree_four_parts]
  simp [pointFour]

theorem pointFour_unique (m a b c : ℕ) (P : Point3 → Prop)
    (hu : ∀ p, P p → ∀ t q, aperyWeight a b c p = t*m+aperyWeight a b c q →
      t=0 ∧ q=p) (p : Point3) (hp : P p) (v : FourCoeff)
    (he : degree ![m,a,b,c] (pointFour p) = degree ![m,a,b,c] v) :
    v = pointFour p := by
  rw [degree_pointFour,degree_four_parts] at he
  obtain ⟨ht,hq⟩ := hu p hp (v 0) ⟨v 1,v 2,v 3⟩ he
  have hx := congrArg Point3.x hq
  have hy := congrArg Point3.y hq
  have hz := congrArg Point3.z hq
  funext i
  fin_cases i <;> simp_all [pointFour]

theorem pointFour_base_isolated (m a b c : ℕ) (P : Point3 → Prop)
    (hu : ∀ p, P p → ∀ t q, aperyWeight a b c p = t*m+aperyWeight a b c q →
      t=0 ∧ q=p) (p : Point3)
    (hx : 0 < p.x → P (Point3.pred1 p))
    (hy : 0 < p.y → P (Point3.pred2 p))
    (hz : 0 < p.z → P (Point3.pred3 p))
    (v : FourCoeff) (hb : BaseEdge ![m,a,b,c] (degree ![m,a,b,c] (pointFour p)) (pointFour p) v) :
    v = pointFour p := by
  apply base_isolated_of_unique_predecessors ![m,a,b,c] (pointFour p) ?_ v hb
  intro i hi w he
  fin_cases i
  · simp [pointFour] at hi
  · have hp : 0 < p.x := by simpa [pointFour] using hi
    have hid : pointFour p-Pi.single (1 : Fin 4) 1 = pointFour (Point3.pred1 p) := by
      funext j
      fin_cases j <;> simp [pointFour,Point3.pred1,Pi.single_apply]
    change degree ![m,a,b,c] (pointFour p-Pi.single (1 : Fin 4) 1) = degree ![m,a,b,c] w at he
    change w = pointFour p-Pi.single (1 : Fin 4) 1
    rw [hid] at he ⊢
    exact pointFour_unique m a b c P hu _ (hx hp) w he
  · have hp : 0 < p.y := by simpa [pointFour] using hi
    have hid : pointFour p-Pi.single (2 : Fin 4) 1 = pointFour (Point3.pred2 p) := by
      funext j
      fin_cases j <;> simp [pointFour,Point3.pred2,Pi.single_apply]
    change degree ![m,a,b,c] (pointFour p-Pi.single (2 : Fin 4) 1) = degree ![m,a,b,c] w at he
    change w = pointFour p-Pi.single (2 : Fin 4) 1
    rw [hid] at he ⊢
    exact pointFour_unique m a b c P hu _ (hy hp) w he
  · have hp : 0 < p.z := by simpa [pointFour] using hi
    have hid : pointFour p-Pi.single (3 : Fin 4) 1 = pointFour (Point3.pred3 p) := by
      funext j
      fin_cases j <;> simp [pointFour,Point3.pred3,Pi.single_apply]
    change degree ![m,a,b,c] (pointFour p-Pi.single (3 : Fin 4) 1) = degree ![m,a,b,c] w at he
    change w = pointFour p-Pi.single (3 : Fin 4) 1
    rw [hid] at he ⊢
    exact pointFour_unique m a b c P hu _ (hz hp) w he

theorem border_intrinsic_lower (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (B : Finset Point3) (P : Point3 → Prop)
    (hu : ∀ p, P p → ∀ t q, aperyWeight a b c p = t*m+aperyWeight a b c q → t=0 ∧ q=p)
    (hi : Set.InjOn (aperyWeight a b c) (B : Set Point3))
    (hv : ∀ p ∈ B, ∃ t q, 0 < t ∧ aperyWeight a b c p = t*m+aperyWeight a b c q)
    (hp : ∀ p ∈ B, (0 < p.x → P (Point3.pred1 p)) ∧
      (0 < p.y → P (Point3.pred2 p)) ∧ (0 < p.z → P (Point3.pred3 p))) :
    B.card ≤ intrinsicRho (generatedSemigroup m a b c) := by
  classical
  have hcard : (B.image pointFour).card = B.card :=
    Finset.card_image_of_injective B pointFour_injective
  rw [← hcard]
  apply isolated_degrees_intrinsic_lower m a b c h (B.image pointFour)
  · intro u huB v hvB he
    obtain ⟨p,hpB,rfl⟩ := Finset.mem_image.mp huB
    obtain ⟨q,hqB,rfl⟩ := Finset.mem_image.mp hvB
    rw [degree_pointFour,degree_pointFour] at he
    exact congrArg pointFour (hi hpB hqB he)
  · intro u huB
    obtain ⟨p,hpB,rfl⟩ := Finset.mem_image.mp huB
    obtain ⟨t,q,ht,he⟩ := hv p hpB
    let v : FourCoeff := ![t,q.x,q.y,q.z]
    refine ⟨v,?_,?_⟩
    · rw [degree_pointFour,degree_four_parts]
      simpa [v] using he
    · intro hh
      have h0 := congrFun hh (0 : Fin 4)
      simp [pointFour,v] at h0
      omega
  · intro u huB v hb
    obtain ⟨p,hpB,rfl⟩ := Finset.mem_image.mp huB
    obtain ⟨hx,hy,hz⟩ := hp p hpB
    exact pointFour_base_isolated m a b c P hu p hx hy hz v hb

theorem even_family_rho_lower (m k : ℕ) (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) :
    2*k+4 ≤ intrinsicRho (generatedSemigroup m (evenA m k) (evenB m k) (evenC m k)) := by
  let L := m-k*k-k
  have ht : k*k+2*k+1 ≤ m := by nlinarith
  have hL : k < L := by dsimp [L]; omega
  have hrel : L+k*k+k=m := by dsimp [L]; omega
  have hpm : 0 < (k+1)*m := Nat.mul_pos (by omega) (by nlinarith)
  have ha : evenA m k+1=(k+1)*m := by unfold evenA; omega
  have hc := even_minimalFour m k hk hm
  have hl := border_intrinsic_lower m (evenA m k) (evenB m k) (evenC m k) hc
    (evenBorder L k) (EvenRegion L k)
    (fun p hp t q he => even_unique_factorization m k L (evenA m k) (evenB m k)
      (evenC m k) (by omega) hL hrel ha rfl rfl hc.coprime hp t he)
    (evenBorder_weight_injective m k hk hm) (evenBorder_reduction m k hk hm)
    (fun p hp => evenBorder_predecessors L k hk hL hp)
  simpa only [evenBorder_card L k hk hL] using hl

theorem odd_family_rho_lower (m k : ℕ) (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) :
    2*k+3 ≤ intrinsicRho (generatedSemigroup m (oddA m k) (oddB m k) (oddC m k)) := by
  let L := m-k*k-1
  have hL : k ≤ L := by dsimp [L]; omega
  have hrel : L+k*k+1=m := by dsimp [L]; omega
  have hpm : 0 < k*m := Nat.mul_pos (by omega) (by nlinarith)
  have ha : oddA m k+1=k*m := by unfold oddA; omega
  have hc := odd_minimalFour m k hk hm
  have hl := border_intrinsic_lower m (oddA m k) (oddB m k) (oddC m k) hc
    (oddBorder L k) (OddRegion L k)
    (fun p hp t q he => odd_unique_factorization m k L (oddA m k) (oddB m k)
      (oddC m k) hk hL hrel ha rfl rfl hc.coprime hp t he)
    (oddBorder_weight_injective m k hk hm) (oddBorder_reduction m k hk hm)
    (fun p hp => oddBorder_predecessors L k hk hL hp)
  simpa only [oddBorder_card L k hk hL] using hl

end NSP3.Sharpness

namespace NSP3

open Sharpness

theorem all_m_sharp_attainment (m : ℕ) (hm : 4 ≤ m) :
    ∃ S : AddSubmonoid ℕ,
      ((S : Set ℕ)ᶜ).Finite ∧
      semigroupEmbeddingDimension (S : Set ℕ) = 4 ∧
      IsSemigroupMultiplicity (S : Set ℕ) m ∧
      intrinsicRho (S : Set ℕ) =
        ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ := by
  rcases real_floor_parameter_split hm with ⟨k,hk,heta,hbound⟩ | ⟨k,hk,heta,hbound⟩
  · have h := even_minimalFour m k hk hbound
    have hs := minimal_generator_class_bridge m (evenA m k) (evenB m k) (evenC m k) h
    refine ⟨generatedAddSubmonoid m (evenA m k) (evenB m k) (evenC m k),
      hs.2.2.2,hs.2.2.1,hs.1,?_⟩
    change intrinsicRho (generatedSemigroup m (evenA m k) (evenB m k) (evenC m k)) = _
    apply le_antisymm (intrinsic_rho_real_sharp m (evenA m k) (evenB m k) (evenC m k) h)
    rw [heta]
    exact even_family_rho_lower m k hk hbound
  · have h := odd_minimalFour m k hk hbound
    have hs := minimal_generator_class_bridge m (oddA m k) (oddB m k) (oddC m k) h
    refine ⟨generatedAddSubmonoid m (oddA m k) (oddB m k) (oddC m k),
      hs.2.2.2,hs.2.2.1,hs.1,?_⟩
    change intrinsicRho (generatedSemigroup m (oddA m k) (oddB m k) (oddC m k)) = _
    apply le_antisymm (intrinsic_rho_real_sharp m (oddA m k) (oddB m k) (oddC m k) h)
    rw [heta]
    exact odd_family_rho_lower m k hk hbound

/-- Actual rho values of cofinite embedding-dimension-four submonoids at multiplicity m. -/
def sharpRhoValues (m : ℕ) : Set ℕ :=
  {r | ∃ S : AddSubmonoid ℕ, ((S : Set ℕ)ᶜ).Finite ∧
    semigroupEmbeddingDimension (S : Set ℕ) = 4 ∧
    IsSemigroupMultiplicity (S : Set ℕ) m ∧ intrinsicRho (S : Set ℕ) = r}

theorem all_m_rho_values_isGreatest (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (sharpRhoValues m) ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ := by
  constructor
  · exact all_m_sharp_attainment m hm
  · rintro r ⟨S,hcof,hedim,hmult,hr⟩
    rw [← hr]
    exact numerical_semigroup_all_edim4_rho_upper S m hcof hedim hmult

theorem all_m_rho_values_nonempty (m : ℕ) (hm : 4 ≤ m) : (sharpRhoValues m).Nonempty :=
  ⟨_,(all_m_rho_values_isGreatest m hm).1⟩

theorem all_m_rho_values_bddAbove (m : ℕ) (hm : 4 ≤ m) : BddAbove (sharpRhoValues m) :=
  ⟨_,(all_m_rho_values_isGreatest m hm).2⟩

theorem all_m_rho_values_sSup (m : ℕ) (hm : 4 ≤ m) :
    sSup (sharpRhoValues m) = ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  (all_m_rho_values_isGreatest m hm).csSup_eq

end NSP3
