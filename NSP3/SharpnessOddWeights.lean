import NSP3.SharpnessBorders
import NSP3.SharpnessFamilies

namespace NSP3.Sharpness

private def oddCode (m k : ℕ) (p : Point3) : ℤ :=
  evenIndex k p + if p.y=0 ∧ p.z=0 then (m : ℤ) else 0

private theorem bounded_multiple {n d : ℤ} (hn : 0 < n) (hl : -n < d) (hu : d < n)
    (hd : n  ∣  d) : d=0 := by
  obtain ⟨t,rfl⟩ := hd
  by_cases ht : t=0
  · simp [ht]
  · by_cases hp : 0 < t
    · have : 1 ≤ t := by omega
      nlinarith
    · have : t ≤ -1 := by omega
      nlinarith

private theorem code_data (m k L : ℕ) (hm : L+k*k+1=m)
    {p : Point3} (hp : p ∈ oddBorder L k) :
    (p=⟨1,0,1⟩ ∧ oddCode m k p=k) ∨
    (p=⟨L+1,0,0⟩ ∧ oddCode m k p=(k : ℤ)*k) ∨
    (p=⟨0,k+1,0⟩ ∧ oddCode m k p=(k : ℤ)*k+k) ∨
    (∃ j, 1 ≤ j ∧ j ≤ k ∧ p=⟨j,k+1-j,0⟩ ∧
      oddCode m k p=((k : ℤ)+1)*(k-j)) ∨
    (∃ j, 1 ≤ j ∧ j ≤ k ∧ p=⟨0,k-j,j⟩ ∧
      oddCode m k p=(k : ℤ)*k+j) := by
  have hm' : (L : ℤ)+(k : ℤ)*k+1=m := by exact_mod_cast hm
  rcases (oddBorder_mem L k p).mp hp with rfl | rfl | rfl |
    ⟨j,hj,hjk,rfl⟩ | ⟨j,hj,hjk,rfl⟩
  · left; constructor
    · rfl
    · simp [oddCode,evenIndex]
  · right; left; constructor
    · rfl
    · simp [oddCode,evenIndex]; omega
  · right; right; left; constructor
    · rfl
    · simp [oddCode,evenIndex]; ring
  · right; right; right; left
    refine ⟨j,hj,hjk,rfl,?_⟩
    have hy : k+1-j ≠ 0 := by omega
    simp [oddCode,evenIndex,hy,Nat.cast_sub (show j ≤ k+1 by omega)]
    ring
  · right; right; right; right
    refine ⟨j,hj,hjk,rfl,?_⟩
    have hj0 : j ≠ 0 := by omega
    simp [oddCode,evenIndex,hj0,Nat.cast_sub hjk]
    ring

private theorem left_bounds (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    0  ≤  ((k : ℤ)+1)*(k-j) ∧ ((k : ℤ)+1)*(k-j)  ≤  (k : ℤ)*k-1 := by
  have hk : (0 : ℤ)  ≤  k := by omega
  have hj' : (1 : ℤ)  ≤  j := by exact_mod_cast hj
  have hjk' : (j : ℤ)  ≤  k := by exact_mod_cast hjk
  constructor
  · exact mul_nonneg (by omega) (by omega)
  · nlinarith [mul_nonneg (by omega : (0 : ℤ)  ≤  k+1)
      (by omega : (0 : ℤ)  ≤  j-1)]

private theorem code_bounds (m k L : ℕ) (hk : 2 ≤ k) (hm : L+k*k+1=m)
    (hmk : k*k+k+1 ≤ m) {p : Point3} (hp : p ∈ oddBorder L k) :
    0  ≤  oddCode m k p ∧ oddCode m k p  <  m := by
  have hmk' : (k : ℤ)*k+k+1 ≤ m := by exact_mod_cast hmk
  rcases code_data m k L hm hp with ⟨_,he⟩ | ⟨_,he⟩ | ⟨_,he⟩ |
    ⟨j,hj,hjk,_,he⟩ | ⟨j,hj,hjk,_,he⟩  <;> rw [he]
  · constructor  <;> nlinarith [sq_nonneg (k : ℤ)]
  · constructor  <;> nlinarith [sq_nonneg (k : ℤ)]
  · constructor  <;> nlinarith [sq_nonneg (k : ℤ)]
  · have hh := left_bounds k j hj hjk
    constructor  <;> nlinarith
  · have hj' : (1 : ℤ)  ≤  j := by exact_mod_cast hj
    have hjk' : (j : ℤ)  ≤  k := by exact_mod_cast hjk
    constructor  <;> nlinarith [sq_nonneg (k : ℤ)]

private theorem code_cast (m k : ℕ) (p : Point3) :
    (oddCode m k p : ZMod m)=(evenIndex k p : ZMod m) := by
  unfold oddCode
  split_ifs  <;> push_cast  <;> simp

private theorem left_ne_A (k j : ℕ) (hk : 2 ≤ k) :
    ((k : ℤ)+1)*(k-j) ≠ k := by
  intro he
  have hd : (k : ℤ)+1  ∣  (k : ℤ) := ⟨(k : ℤ)-j,he.symm⟩
  have hh := bounded_multiple (by omega : (0 : ℤ) < k+1)
    (by omega : -((k : ℤ)+1) < k) (by omega : (k : ℤ) < k+1) hd
  omega

set_option maxHeartbeats 1000000 in
/-- Distinct odd-family border points have distinct actual numerical weights. -/
theorem oddBorder_weight_injective (m k : ℕ) (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) :
    Set.InjOn (aperyWeight (oddA m k) (oddB m k) (oddC m k))
      (oddBorder (m-k*k-1) k) := by
  let L := m-k*k-1
  let a := oddA m k
  let b := oddB m k
  let c := oddC m k
  have hL : k ≤ L := by dsimp [L]; omega
  have hLm : L+k*k+1=m := by dsimp [L]; omega
  have hmpos : 0 < m := by nlinarith
  have ha : a+1=k*m := by
    dsimp [a,oddA]
    have hkm : 1 ≤ k*m := by nlinarith
    omega
  have hb : b=L*m+k := rfl
  have hc : c=b+1 := rfl
  have hbk : k < b := by nlinarith [Nat.mul_pos (show 0 < L by omega) hmpos]
  have hk' : (2 : ℤ) ≤ k := by exact_mod_cast hk
  intro p hp q hq hw
  have hres : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q := by
    rw [← aperyWeight_cast,← aperyWeight_cast]
    exact congrArg (fun n : ℕ => (n : ZMod m)) hw
  rw [odd_residue_index m k L a b c ha hb hc,
    odd_residue_index m k L a b c ha hb hc] at hres
  have hcast : (oddCode m k p : ZMod m)=(oddCode m k q : ZMod m) := by
    rw [code_cast,code_cast]; exact hres
  have hpbound := code_bounds m k L hk hLm hm hp
  have hqbound := code_bounds m k L hk hLm hm hq
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mp hcast
  have hm' : (0 : ℤ) < m := by exact_mod_cast hmpos
  have he : oddCode m k p=oddCode m k q := by
    have hh := bounded_multiple hm' (by omega : -(m : ℤ) < oddCode m k q-oddCode m k p)
      (by omega : oddCode m k q-oddCode m k p < m) hd
    omega
  change aperyWeight a b c p=aperyWeight a b c q at hw
  have hpd := code_data m k L hLm hp
  have hqd := code_data m k L hLm hq
  clear hres hcast hpbound hqbound hd hm' ha hb hL hLm hm hmpos hp hq
  clear_value a b c L
  rcases hpd with ⟨rfl,hpc⟩ | ⟨rfl,hpc⟩ | ⟨rfl,hpc⟩ |
    ⟨j,hj,hjk,rfl,hpc⟩ | ⟨j,hj,hjk,rfl,hpc⟩  <;>
    rcases hqd with ⟨rfl,hqc⟩ | ⟨rfl,hqc⟩ | ⟨rfl,hqc⟩ |
    ⟨l,hl,hlk,rfl,hqc⟩ | ⟨l,hl,hlk,rfl,hqc⟩
  all_goals try rfl
  all_goals rw [hpc,hqc] at he
  all_goals try have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  all_goals try have hjk' : (j : ℤ) ≤ k := by exact_mod_cast hjk
  all_goals try have hl' : (1 : ℤ) ≤ l := by exact_mod_cast hl
  all_goals try have hlk' : (l : ℤ) ≤ k := by exact_mod_cast hlk
  all_goals try have hjb := left_bounds k j hj hjk
  all_goals try have hlb := left_bounds k l hl hlk
  all_goals try have hjA := left_ne_A k j hk
  all_goals try have hlA := left_ne_A k l hk
  all_goals try (exfalso; exact hjA he)
  all_goals try (exfalso; exact hlA he.symm)
  all_goals try (exfalso; nlinarith)
  all_goals try (
    have hij : j=l := by
      have hh : (k : ℤ)-j=(k : ℤ)-l := mul_left_cancel₀ (by omega : (k : ℤ)+1 ≠ 0) he
      omega
    subst l
    rfl)
  all_goals try (
    have hij : j=l := by omega
    subst l
    rfl)
  all_goals try (
    have hll : l=k := by omega
    subst l)
  all_goals try (
    have hjj : j=k := by omega
    subst j)
  all_goals simp only [aperyWeight,Nat.sub_self,mul_zero,add_zero,
    zero_add] at hw
  all_goals have hcl := congrArg (fun n => n*k) hc
  all_goals nlinarith

end NSP3.Sharpness





