import NSP3.V03.SpectrumFamilies

namespace NSP3.V03

open NSP3.Sharpness

def fiveA (r : ℕ) : ℕ := 4*(r+4)-1
def fiveB (r : ℕ) : ℕ := (2*r+1)*(r+4)+2
def fiveC (r : ℕ) : ℕ := (2*r+2)*(r+4)+1
def FiveRegion (r : ℕ) (p : Point3) : Prop :=
  (p.y=0 ∧ p.z=0 ∧ p.x≤r) ∨ (p.x=0 ∧ p.y≤1 ∧ p.z≤1)
def FivePredRegion (r : ℕ) (p : Point3) : Prop :=
  (p.y=0 ∧ p.z=0 ∧ p.x≤r) ∨ p=⟨0,1,0⟩ ∨ p=⟨0,0,1⟩
def fiveBorder (r : ℕ) : Finset Point3 :=
  {⟨r+1,0,0⟩,⟨1,1,0⟩,⟨1,0,1⟩,⟨0,2,0⟩,⟨0,0,2⟩}
def fiveIndex (p : Point3) : ℤ := -(p.x : ℤ)+2*p.y+p.z

theorem fiveA_eq (r : ℕ) : fiveA r=4*r+15 := by unfold fiveA; omega

theorem five_gcd (r : ℕ) :
    Nat.gcd (r+4) (Nat.gcd (fiveA r) (Nat.gcd (fiveB r) (fiveC r)))=1 := by
  let d := Nat.gcd (r+4) (Nat.gcd (fiveA r) (Nat.gcd (fiveB r) (fiveC r)))
  have hdm : d ∣ r+4 := Nat.gcd_dvd_left _ _
  have hdbc : d ∣ Nat.gcd (fiveB r) (fiveC r) :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hdb : d ∣ fiveB r := hdbc.trans (Nat.gcd_dvd_left _ _)
  have hdc : d ∣ fiveC r := hdbc.trans (Nat.gcd_dvd_right _ _)
  have hcb : fiveC r+1=fiveB r+(r+4) := by unfold fiveB fiveC; ring
  have hdcb : d ∣ fiveC r+1 := by rw [hcb]; exact dvd_add hdb hdm
  have hd1 : d ∣ 1 := (Nat.dvd_add_iff_right hdc).mpr hdcb
  exact Nat.dvd_one.mp hd1

theorem five_border_card (r : ℕ) : (fiveBorder r).card=5 := by simp [fiveBorder]

theorem five_outside_dominates (r : ℕ) (p : Point3) (hp : ¬ FiveRegion r p) :
    ∃ b ∈ fiveBorder r, b≤p := by
  by_cases hy : 2≤p.y
  · refine ⟨⟨0,2,0⟩,by simp [fiveBorder],?_⟩
    change 0≤p.x ∧ 2≤p.y ∧ 0≤p.z
    omega
  by_cases hz : 2≤p.z
  · refine ⟨⟨0,0,2⟩,by simp [fiveBorder],?_⟩
    change 0≤p.x ∧ 0≤p.y ∧ 2≤p.z
    omega
  by_cases hx : p.x=0
  · simp [FiveRegion,hx] at hp
    omega
  by_cases hy0 : p.y=0
  · by_cases hz0 : p.z=0
    · refine ⟨⟨r+1,0,0⟩,by simp [fiveBorder],?_⟩
      simp [FiveRegion,hy0,hz0] at hp
      change r+1≤p.x ∧ 0≤p.y ∧ 0≤p.z
      omega
    · refine ⟨⟨1,0,1⟩,by simp [fiveBorder],?_⟩
      change 1≤p.x ∧ 0≤p.y ∧ 1≤p.z
      omega
  · refine ⟨⟨1,1,0⟩,by simp [fiveBorder],?_⟩
    change 1≤p.x ∧ 1≤p.y ∧ 0≤p.z
    omega

theorem five_border_predecessors (r : ℕ) (hr : 1≤r) (p : Point3)
    (hp : p ∈ fiveBorder r) :
    (0<p.x → FivePredRegion r p.pred1) ∧
    (0<p.y → FivePredRegion r p.pred2) ∧
    (0<p.z → FivePredRegion r p.pred3) := by
  simp only [fiveBorder,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [FivePredRegion,Point3.pred1,Point3.pred2,Point3.pred3] <;> omega

theorem five_pred_region (r : ℕ) {p : Point3} (hp : FivePredRegion r p) : FiveRegion r p := by
  rcases hp with hp | rfl | rfl
  · exact Or.inl hp
  · simp [FiveRegion]
  · simp [FiveRegion]

theorem five_border_reductions (r : ℕ) :
    aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨r+1,0,0⟩ =
      aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨0,1,1⟩ ∧
    aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨1,1,0⟩ =
      aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨0,0,1⟩+3*(r+4) ∧
    aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨1,0,1⟩ = (2*r+6)*(r+4) ∧
    aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨0,2,0⟩ =
      aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨r,0,0⟩+3*(r+4) ∧
    aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨0,0,2⟩ =
      aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨0,1,0⟩+(2*r+3)*(r+4) := by
  simp only [aperyWeight,fiveA_eq,fiveB,fiveC]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private theorem not_weight_minimal_drop (m a b c : ℕ) (hm : 0 < m)
    (p q : Point3) (t : ℕ) (ht : 0<t)
    (he : aperyWeight a b c p=aperyWeight a b c q+t*m) :
    ¬ WeightMinimal m a b c p := by
  intro hp
  have he' := congrArg (fun n : ℕ => (n : ZMod m)) he
  push_cast at he'
  simp only [ZMod.natCast_self,mul_zero,add_zero] at he'
  have hr : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p := by
    rw [← aperyWeight_cast,← aperyWeight_cast]
    exact he'.symm
  have hw := hp q hr
  nlinarith

theorem five_nonpure_border_not_minimal (r : ℕ) (p : Point3) (hp : p ∈ fiveBorder r)
    (hne : p≠⟨r+1,0,0⟩) :
    ¬ WeightMinimal (r+4) (fiveA r) (fiveB r) (fiveC r) p := by
  obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := five_border_reductions r
  simp only [fiveBorder,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · exact not_weight_minimal_drop _ _ _ _ (by omega) _ _ 3 (by omega) h₁
  · apply not_weight_minimal_drop _ _ _ _ (by omega) _ ⟨0,0,0⟩ (2*r+6) (by omega)
    simpa [aperyWeight] using h₂
  · exact not_weight_minimal_drop _ _ _ _ (by omega) _ _ 3 (by omega) h₃
  · exact not_weight_minimal_drop _ _ _ _ (by omega) _ _ (2*r+3) (by omega) h₄

theorem five_border_not_canonical (r : ℕ) (p : Point3) (hp : p ∈ fiveBorder r) :
    ¬ AperyCanonical (r+4) (fiveA r) (fiveB r) (fiveC r) p := by
  intro hc
  by_cases he : p=⟨r+1,0,0⟩
  · subst p
    have hw := (five_border_reductions r).1
    have hres : residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
        (fiveC r : ZMod (r+4)) ⟨0,1,1⟩ =
        residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
        (fiveC r : ZMod (r+4)) ⟨r+1,0,0⟩ := by
      rw [← aperyWeight_cast,← aperyWeight_cast,hw]
    have hlt : aperyKey (fiveA r) (fiveB r) (fiveC r) ⟨0,1,1⟩ <
        aperyKey (fiveA r) (fiveB r) (fiveC r) ⟨r+1,0,0⟩ := by
      unfold aperyKey
      rw [hw]
      exact Prod.Lex.right _ (Prod.Lex.left _ _ (by change 0<r+1; omega))
    exact (not_lt_of_ge (hc _ hres)) hlt
  · exact five_nonpure_border_not_minimal r p hp he
      (fun q hq => aperyCanonical_weight_min _ _ _ _ hc hq)

theorem five_canonical_region (r : ℕ) (p : Point3)
    (hp : AperyCanonical (r+4) (fiveA r) (fiveB r) (fiveC r) p) : FiveRegion r p := by
  by_contra hn
  obtain ⟨b,hb,hbp⟩ := five_outside_dominates r p hn
  exact five_border_not_canonical r b hb (aperyCanonical_downward _ _ _ _ hbp hp)

theorem five_index_injective (r : ℕ) {p q : Point3}
    (hp : FiveRegion r p) (hq : FiveRegion r q) (he : fiveIndex p=fiveIndex q) : p=q := by
  unfold FiveRegion at hp hq
  unfold fiveIndex at he
  rcases hp with ⟨py,pz,px⟩ | ⟨px,py,pz⟩ <;>
    rcases hq with ⟨qy,qz,qx⟩ | ⟨qx,qy,qz⟩ <;>
    apply Point3.ext <;> simp_all <;> omega

theorem five_index_bounds (r : ℕ) {p : Point3} (hp : FiveRegion r p) :
    -(r : ℤ)≤fiveIndex p ∧ fiveIndex p≤3 := by
  rcases hp with ⟨hy,hz,hx⟩ | ⟨hx,hy,hz⟩ <;> simp [fiveIndex,hy,hz,hx] <;> omega

theorem five_residue_index (r : ℕ) (p : Point3) :
    residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
      (fiveC r : ZMod (r+4)) p = (fiveIndex p : ZMod (r+4)) := by
  have ha : fiveA r+1=4*(r+4) := by rw [fiveA_eq]; omega
  have hmod : ((r+4 : ℕ) : ZMod (r+4))=0 := ZMod.natCast_self _
  have ha' := congrArg (fun n : ℕ => (n : ZMod (r+4))) ha
  rw [Nat.cast_add,Nat.cast_one,Nat.cast_mul,hmod,mul_zero] at ha'
  have hA : (fiveA r : ZMod (r+4))=-1 := by linear_combination ha'
  have hB : (fiveB r : ZMod (r+4))=2 := by
    unfold fiveB
    rw [Nat.cast_add,Nat.cast_mul,hmod,mul_zero,zero_add]
    norm_num
  have hC : (fiveC r : ZMod (r+4))=1 := by
    unfold fiveC
    rw [Nat.cast_add,Nat.cast_mul,hmod,mul_zero,zero_add]
    norm_num
  simp only [residueOf,fiveIndex,Int.cast_add,Int.cast_neg,Int.cast_mul,Int.cast_natCast,
    Int.cast_ofNat]
  rw [hA,hB,hC]
  ring

theorem five_residue_injective (r : ℕ) {p q : Point3}
    (hp : FiveRegion r p) (hq : FiveRegion r q)
    (he : residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
      (fiveC r : ZMod (r+4)) p =
      residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
      (fiveC r : ZMod (r+4)) q) : p=q := by
  rw [five_residue_index,five_residue_index] at he
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (r+4)).mp he
  have hp' := five_index_bounds r hp
  have hq' := five_index_bounds r hq
  obtain ⟨k,hk⟩ := hd
  push_cast at hk
  have heI : fiveIndex q-fiveIndex p=0 := by
    by_cases hz : k=0
    · simp_all
    · by_cases hs : 0<k
      · have : 1≤k := by omega
        have : (0 : ℤ)≤r := by omega
        nlinarith
      · have : k≤-1 := by omega
        have : (0 : ℤ)≤r := by omega
        nlinarith
  exact five_index_injective r hp hq (by omega)

theorem five_canonical_iff (r : ℕ) (p : Point3) :
    AperyCanonical (r+4) (fiveA r) (fiveB r) (fiveC r) p ↔ FiveRegion r p := by
  constructor
  · exact five_canonical_region r p
  · intro hp
    let q := aperyRepresentative (r+4) (fiveA r) (fiveB r) (fiveC r) (by omega)
      (five_gcd r) (residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
        (fiveC r : ZMod (r+4)) p)
    have hs := aperyRepresentative_spec (r+4) (fiveA r) (fiveB r) (fiveC r) (by omega)
      (five_gcd r) (residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
        (fiveC r : ZMod (r+4)) p)
    have he : q=p := five_residue_injective r (five_canonical_region r q hs.2) hp hs.1
    exact he ▸ hs.2

end NSP3.V03
