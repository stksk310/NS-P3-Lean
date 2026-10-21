import NSP3.SharpnessFamilies
import NSP3.SharpnessBorders

namespace NSP3.Sharpness

theorem evenBorder_reduction (m k : ℕ) (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) :
    ∀ p ∈ evenBorder (m-k*k-k) k, ∃ t q, 0 < t ∧
      aperyWeight (evenA m k) (evenB m k) (evenC m k) p =
        t*m+aperyWeight (evenA m k) (evenB m k) (evenC m k) q := by
  have hm4 : 4 ≤ m := by nlinarith
  have hthreshold : k*k+2*k+1 ≤ m := by nlinarith
  have hkk : k*k ≤ m := by omega
  have hkrem : k ≤ m-k*k := by omega
  have hL : k+1 ≤ m-k*k-k := by omega
  have hpm : 1 ≤ (k+1)*m := by nlinarith [Nat.mul_le_mul_right m hk]
  intro p hp
  rw [evenBorder_mem] at hp
  rcases hp with rfl | rfl | ⟨j,hj,rfl⟩ | ⟨j,hj,hjk,rfl⟩
  · refine ⟨k+1,⟨0,1,0⟩,by omega,?_⟩
    dsimp [aperyWeight,evenA,evenB,evenC]
    zify [hkk,hkrem,hpm]
    ring
  · refine ⟨m-k*k-k-1,⟨0,0,k⟩,by omega,?_⟩
    dsimp [aperyWeight,evenA,evenB,evenC]
    zify [hkk,hkrem,hpm,show 1 ≤ m-k*k-k by omega]
    ring
  · refine ⟨m-k*k-k+(k+1)*j,⟨0,0,k-j⟩,by omega,?_⟩
    dsimp [aperyWeight,evenA,evenB,evenC]
    zify [hkk,hkrem,hpm,hj,show j ≤ k+1 by omega]
    ring
  · refine ⟨(k+1)*j+1,⟨m-k*k-k-j,0,0⟩,by omega,?_⟩
    dsimp [aperyWeight,evenA,evenB,evenC]
    zify [hkk,hkrem,hpm,hjk,show j ≤ m-k*k-k by omega]
    ring

theorem oddBorder_reduction (m k : ℕ) (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) :
    ∀ p ∈ oddBorder (m-k*k-1) k, ∃ t q, 0 < t ∧
      aperyWeight (oddA m k) (oddB m k) (oddC m k) p =
        t*m+aperyWeight (oddA m k) (oddB m k) (oddC m k) q := by
  have hm7 : 7 ≤ m := by nlinarith
  have hkk : k*k ≤ m := by omega
  have hkrem : 1 ≤ m-k*k := by omega
  have hL : k ≤ m-k*k-1 := by omega
  have hpm : 1 ≤ k*m := by nlinarith [Nat.mul_le_mul_right m hk]
  intro p hp
  rw [oddBorder_mem] at hp
  rcases hp with rfl | rfl | rfl | ⟨j,hj,hjk,rfl⟩ | ⟨j,hj,hjk,rfl⟩
  · refine ⟨k,⟨0,1,0⟩,by omega,?_⟩
    dsimp [aperyWeight,oddA,oddB,oddC]
    zify [hkk,hkrem,hpm]
    ring
  · refine ⟨k-1,⟨0,k,0⟩,by omega,?_⟩
    dsimp [aperyWeight,oddA,oddB,oddC]
    zify [hkk,hkrem,hpm,show 1 ≤ k by omega]
    ring
  · refine ⟨m-k,⟨m-k*k-1-k+1,0,0⟩,by omega,?_⟩
    dsimp [aperyWeight,oddA,oddB,oddC]
    zify [hkk,hkrem,hpm,hL,show k ≤ m by omega]
    ring
  · refine ⟨m-k*k-1+k*j,⟨0,0,k-j⟩,by omega,?_⟩
    dsimp [aperyWeight,oddA,oddB,oddC]
    zify [hkk,hkrem,hpm,hjk,show j ≤ k+1 by omega]
    ring
  · refine ⟨k*(j-1)+1,⟨m-k*k-1+1-j,0,0⟩,by omega,?_⟩
    dsimp [aperyWeight,oddA,oddB,oddC]
    zify [hkk,hkrem,hpm,hjk,hj,show j ≤ m-k*k-1+1 by omega]
    ring




private theorem affine_chain_injective (a b n i j : ℕ) (hi : i ≤ n) (hj : j ≤ n)
    (hab : a < b) (he : a*i+b*(n-i)=a*j+b*(n-j)) : i=j := by
  zify [hi,hj] at he
  have hh : ((a:ℤ)-b)*((i:ℤ)-j)=0 := by nlinarith only [he]
  rcases mul_eq_zero.mp hh with h | h
  · have : (a:ℤ) < b := by exact_mod_cast hab
    omega
  · exact_mod_cast (show (i:ℤ)=j by omega)

private theorem even_injective_criterion (m a b c L k d : ℕ)
    (hm : 0 < m) (ha : 2 ≤ a) (hab : a+2 ≤ b) (hc : c=b+1)
    (hk : 1 ≤ k) (hd : a+d=b)
    (hbase : L*a+m=(k+1)*b)
    (hacx : a+c ≠ L*a)
    (hdm : ∀ j, j ≤ k → j*d ≠ m) :
    Set.InjOn (aperyWeight a b c) (evenBorder L k : Set Point3) := by
  have hab' : a < b := by omega
  have hleft : ∀ j, j ≤ k → aperyWeight a b c ⟨j,k+1-j,0⟩+j*d=(k+1)*b := by
    intro j hj
    dsimp [aperyWeight]
    have hsub : k+1-j+j=k+1 := by omega
    nlinarith only [hsub,hd]
  have hright : ∀ j, j ≤ k+1 → aperyWeight a b c ⟨0,k+1-j,j⟩=(k+1)*b+j := by
    intro j hj
    dsimp [aperyWeight]
    have hsub : k+1-j+j=k+1 := by omega
    nlinarith only [hsub,hc]
  have hAL : ∀ j, j ≤ k → a+c ≠ aperyWeight a b c ⟨j,k+1-j,0⟩ := by
    intro j hj he
    dsimp [aperyWeight] at he
    by_cases hj0 : j=0
    · subst j; simp only [mul_zero,add_zero,Nat.sub_zero] at he
      nlinarith only [he,hc,hab,hk]
    · have hj1 : 1 ≤ j := by omega
      have hsub : k+1-j+ j=k+1 := by omega
      by_cases hk1 : k=1
      · have : j=1 := by omega
        subst k; subst j; simp at he
        omega
      · have hk2 : 2 ≤ k := by omega
        have hlow : a*(j-1)+b*(k-j) ≥ a := by
          have h1 : j-1+(k-j)=k-1 := by omega
          have h2 : a*(k-j) ≤ b*(k-j) := Nat.mul_le_mul_right _ (by omega : a ≤ b)
          have h3 : a ≤ a*(k-1) := Nat.le_mul_of_pos_right a (by omega)
          have h4 := congrArg (fun v => a*v) h1
          nlinarith only [h2,h3,h4]
        have h1 : j-1+1=j := by omega
        have h2 : k-j+1=k+1-j := by omega
        nlinarith only [he,hc,h1,h2,hlow,ha]
  have hAR : ∀ j, 1 ≤ j → j ≤ k+1 → a+c ≠ aperyWeight a b c ⟨0,k+1-j,j⟩ := by
    intro j hj hjk he
    rw [hright j hjk] at he
    nlinarith only [he,hc,hab,hk,hj]
  have hXL : ∀ j, j ≤ k → L*a ≠ aperyWeight a b c ⟨j,k+1-j,0⟩ := by
    intro j hj he
    have := hleft j hj
    have : j*d=m := by omega
    exact hdm j hj this
  have hXR : ∀ j, 1 ≤ j → j ≤ k+1 → L*a ≠ aperyWeight a b c ⟨0,k+1-j,j⟩ := by
    intro j hj hjk he
    rw [hright j hjk] at he
    omega
  have hLR : ∀ i j, i ≤ k → 1 ≤ j → j ≤ k+1 →
      aperyWeight a b c ⟨i,k+1-i,0⟩ ≠ aperyWeight a b c ⟨0,k+1-j,j⟩ := by
    intro i j hi hj hjk he
    have := hleft i hi
    rw [hright j hjk] at he
    omega
  intro p hp q hq he
  rw [Finset.mem_coe,evenBorder_mem] at hp hq
  rcases hp with rfl | rfl | ⟨i,hi,rfl⟩ | ⟨i,hi,hik,rfl⟩ <;>
    rcases hq with rfl | rfl | ⟨j,hj,rfl⟩ | ⟨j,hj,hjk,rfl⟩
  · rfl
  · exact False.elim (hacx (by simpa [aperyWeight,mul_comm] using he))
  · exact False.elim (hAL j hj (by simpa [aperyWeight,mul_comm] using he))
  · exact False.elim (hAR j hj hjk (by simpa [aperyWeight,mul_comm] using he))
  · exact False.elim (hacx (by simpa [aperyWeight,mul_comm] using he.symm))
  · rfl
  · exact False.elim (hXL j hj (by simpa [aperyWeight,mul_comm] using he))
  · exact False.elim (hXR j hj hjk (by simpa [aperyWeight,mul_comm] using he))
  · exact False.elim (hAL i hi (by simpa [aperyWeight,mul_comm] using he.symm))
  · exact False.elim (hXL i hi (by simpa [aperyWeight,mul_comm] using he.symm))
  · have hij : i=j := affine_chain_injective a b (k+1) i j (by omega) (by omega) hab' (by simpa [aperyWeight,mul_comm] using he)
    subst j; rfl
  · exact False.elim (hLR i j hi hj hjk he)
  · exact False.elim (hAR i hi hik (by simpa [aperyWeight,mul_comm] using he.symm))
  · exact False.elim (hXR i hi hik (by simpa [aperyWeight,mul_comm] using he.symm))
  · exact False.elim (hLR j i hj hi hik he.symm)
  · have hij : i=j := by rw [hright i hik,hright j hjk] at he; omega
    subst j; rfl



theorem evenBorder_weight_injective (m k : ℕ) (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) :
    Set.InjOn (aperyWeight (evenA m k) (evenB m k) (evenC m k))
      (evenBorder (m-k*k-k) k : Set Point3) := by
  let L:=m-k*k-k
  let a:=evenA m k
  let b:=evenB m k
  let c:=evenC m k
  let d:=b-a
  have ht : k*k+2*k+1 ≤ m := by nlinarith
  have hm4 : 4 ≤ m := by nlinarith
  have hkk : k*k ≤ m := by omega
  have hkrem : k ≤ m-k*k := by omega
  have hL : k+1 ≤ L := by dsimp [L]; omega
  have hLeq : L+k*k+k=m := by dsimp [L]; omega
  have hpm : 1 ≤ (k+1)*m := by nlinarith [Nat.mul_le_mul_right m hk]
  have ha : a+1=(k+1)*m := by dsimp [a,evenA]; omega
  have hb : b=L*m+k := by rfl
  have hc : c=b+1 := by rfl
  have hap : 2 ≤ a := by nlinarith only [ha,hk,hm4]
  have hab : a+2 ≤ b := by nlinarith only [ha,hb,hL,hk,hm4]
  have hd : a+d=b := by dsimp [d]; omega
  have hdform : d=(L-(k+1))*m+(k+1) := by
    have hr : L-(k+1)+(k+1)=L := by omega
    nlinarith only [hd,ha,hb,hr]
  have hbase : L*a+m=(k+1)*b := by
    dsimp [a,b,L,evenA,evenB]
    zify [hkk,hkrem,hpm]
    ring
  have hacx : a+c ≠ L*a := by
    intro he
    have haL := congrArg (fun r => L*r) ha
    have heq : (k+1+L)*m+(L+k)=L*((k+1)*m) := by
      nlinarith only [haL,ha,hb,hc,he]
    have hd0 : m ∣ (k+1+L)*m := Nat.dvd_mul_left _ _
    have hd1 : m ∣ (k+1+L)*m+(L+k) := ⟨L*(k+1),by nlinarith only [heq]⟩
    have hd2 : m ∣ L+k := (Nat.dvd_add_iff_right hd0).mpr hd1
    have hpos : 0 < L+k := by omega
    have hlt : L+k < m := by nlinarith only [hLeq,hk]
    have := Nat.le_of_dvd hpos hd2
    omega
  have hdm : ∀ j, j ≤ k → j*d ≠ m := by
    intro j hj he
    by_cases hj0 : j=0
    · simp [hj0] at he; omega
    have hjp : 0 < j*(k+1) := by positivity
    have hjlt : j*(k+1) < m := by nlinarith [Nat.mul_le_mul_right (k+1) hj]
    have hd0 : m ∣ j*((L-(k+1))*m) := ⟨j*(L-(k+1)),by ring⟩
    have hd1 : m ∣ j*((L-(k+1))*m)+j*(k+1) := by
      rw [←mul_add,←hdform,he]
    have hd2 : m ∣ j*(k+1) := (Nat.dvd_add_iff_right hd0).mpr hd1
    have := Nat.le_of_dvd hjp hd2
    omega
  exact even_injective_criterion m a b c L k d (by omega) hap hab hc hk hd hbase hacx hdm

end NSP3.Sharpness

