import NSP3.SymbolicT3Classification

namespace NSP3
open Finset

/-- The three baseline rows are an actual subset of H. -/
theorem t3_equal_height_H_lower (S : CyclicStaircase) {g : Point3}
    (ht : pair23Count S.D=3) (he : pair12Count S.D=pair13Count S.D)
    (hk : 4≤pair12Count S.D) (hh : g.x=pair12Count S.D) :
    3*pair12Count S.D-5≤(fullSupportSymbolicH S g).card := by
  classical
  let k:=pair12Count S.D
  let R : Finset (ℕ×ℕ):={(1,1),(1,2),(2,1)}
  let P:=(Icc 1 (k-2)).product R
  let f : ℕ×(ℕ×ℕ)→Point3:=fun p=>⟨p.1,p.2.1,p.2.2⟩
  have hi : Set.InjOn f P:=by
    intro a _ b _ hab
    exact Prod.ext (congrArg Point3.x hab)
      (Prod.ext (congrArg Point3.y hab) (congrArg Point3.z hab))
  have hsub : P.image f⊆fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨⟨x,⟨u,v⟩⟩,hq,rfl⟩:=mem_image.mp hp
    obtain ⟨hx,huv⟩:=mem_product.mp hq
    have hx':=mem_Icc.mp hx
    have huv' : (u=1 ∧ v=1) ∨ (u=1 ∧ v=2) ∨ (u=2 ∧ v=1):=by
      simpa only [R,mem_insert,mem_singleton,Prod.mk.injEq] using huv
    apply mem_union.mpr;left
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    refine ⟨?_,?_⟩
    · rcases huv' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        simp only [FullCore,f,←he,ht] <;> dsimp [k] at * <;> omega
    · intro hle
      have h:=hle.1
      change g.x≤x at h
      dsimp [k] at hx'
      omega
  have htip : Point3.mk (k-1) 1 1∈fullSupportSymbolicH S g:=by
    apply mem_union.mpr;left
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    refine ⟨?_,?_⟩
    · simp only [FullCore,←he,ht];dsimp [k];omega
    · intro hle;have h:=hle.1;change g.x≤k-1 at h;dsimp [k] at h;omega
  have hnot : Point3.mk (k-1) 1 1∉P.image f:=by
    intro hp
    obtain ⟨p,hp,heq⟩:=mem_image.mp hp
    have hx:=(mem_Icc.mp (mem_product.mp hp).1).2
    have hx':=congrArg Point3.x heq
    change p.1=k-1 at hx'
    dsimp [k] at *
    omega
  have hc:=card_le_card (insert_subset htip hsub)
  rw [card_insert_of_notMem hnot,card_image_of_injOn hi] at hc
  have hcard : P.card=(k-2)*3:=by
    simp [P,R]
  rw [hcard] at hc
  dsimp [k] at hc
  omega

/-- Baseline resources retain the actual yz area and all selected extra columns. -/
theorem t3_equal_height_resource_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (he : pair12Count S.D=pair13Count S.D) (hh : g.x=pair12Count S.D)
    (ht : pair23Count S.D=3) (hk : 4≤pair12Count S.D)
    (hy : g.y=1) (hz : g.z=1) (B : Finset Point3)
    (hB : ∀ p∈B, p.x=0 ∧ 0<p.y ∧ 0<p.z ∧ 3<p.y+p.z ∧ p∈S.D) :
    (pair12Count S.D)^2+5*pair12Count S.D-2+(plane23PosFinset S).card+
      B.sum (fun p=>pair12Count S.D-max p.y p.z) ≤ S.m := by
  have h:=t3_balanced_extra_budget S hg hf he hh ht hy hz B hB
  have hH:=t3_equal_height_H_lower S ht he hk hh
  have hX:=pair12_intercept1_lower S
  have hY:=pair12_intercept2_lower S
  have hZ:=pair12_return_capacity_fullSupport S hg hf
  have h12:=pair12_symbolic_defect_lower S hg hf
  have h13:=pair13_symbolic_defect_lower S hg hf
  have hD12 : 1≤ferrersPlaneDefect (pair12Count S.D) g.x g.y:=le_max_left _ _
  have hD13 : 1≤ferrersPlaneDefect (pair13Count S.D) g.x g.z:=le_max_left _ _
  have hE12 : 1≤(pair12ExtraFinset S).card:=by omega
  have hE13 : 1≤(pair13ExtraFinset S).card:=by omega
  rw [card_plane12PosFinset,card_plane13PosFinset,←he] at h
  have cr : 2*Nat.choose (pair12Count S.D) 2=pair12Count S.D*(pair12Count S.D-1):=by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' (pair12Count S.D).two_dvd_mul_sub_one
  have er : pair12Count S.D-1+1=pair12Count S.D:=by omega
  have eqn : (pair12Count S.D)^2+5*pair12Count S.D=
      2*Nat.choose (pair12Count S.D) 2+6*pair12Count S.D:=by nlinarith [cr,er]
  rw [eqn]
  omega

/-- Both present bases close every equal-height k>=5 at once. -/
theorem t3_balanced_present_ge5_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 5≤pair12Count S.D)
    (hh : g.x=pair12Count S.D) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D) : fullTarget S≤S.m := by
  classical
  have hb:=t3_equal_height_resource_lower S hg hf he hh ht (by omega) hy hz
    {Point3.mk 0 1 3,Point3.mk 0 3 1} (by
      intro p hp
      simp only [mem_insert,mem_singleton] at hp
      rcases hp with rfl | rfl <;> norm_num <;> assumption)
  norm_num at hb
  have ha:=thin23_three_corner_area_lower S hg hf ht hy hz
  have hm : (pair12Count S.D)^2+5*pair12Count S.D+7≤S.m:=by omega
  have hs : (pair12Count S.D+pair12Count S.D+5)^2≤4*S.m:=by nlinarith
  rw [fullTarget_eq_square,←he,ht]
  norm_num only [Nat.add_assoc] at *
  omega

private theorem yz_three_extra_area (S : CyclicStaircase)
    (ht : pair23Count S.D=3) (a b c : Point3) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (h : ∀ p∈({a,b,c}:Finset Point3), p.x=0 ∧ 0<p.y ∧ 0<p.z ∧ 3<p.y+p.z ∧ p∈S.D) :
    6≤(plane23PosFinset S).card := by
  classical
  have hsub : ({a,b,c}:Finset Point3)⊆pair23ExtraFinset S:=by
    intro p hp
    obtain ⟨hx,hy,hz,hs,hd⟩:=h p hp
    exact (mem_pair23ExtraFinset S p).mpr ⟨hd,hx,hy,hz,by omega⟩
  have hc:=card_le_card hsub
  simp [hab,hac,hbc] at hc
  have he:=card_plane23PosFinset S
  rw [ht] at he
  norm_num at he
  omega

/-- Each missing orientation closes all k>=4, including its empty k4 last column. -/
theorem t3_balanced_missing_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 4≤pair12Count S.D)
    (hh : g.x=pair12Count S.D) (hy : g.y=1) (hz : g.z=1)
    (hnot : Point3.mk 0 1 3∉S.D ∨ Point3.mk 0 3 1∉S.D) : fullTarget S≤S.m := by
  classical
  have hY : 5≤pure2Intercept S:=by have:=pair12_intercept2_lower S;omega
  have hZ : 5≤pure3Intercept S:=by have:=pair12_return_capacity_fullSupport S hg hf;omega
  have hm : (pair12Count S.D)^2+5*pair12Count S.D+7≤S.m := by
    rcases hnot with hnot | hnot
    · obtain ⟨h22,h31,h41⟩:=t3_missing13_standard_points S hg hf ht hy hz hY hZ hnot
      have hB : ∀ p∈({Point3.mk 0 2 2,Point3.mk 0 3 1,Point3.mk 0 4 1}:Finset Point3),
          p.x=0 ∧ 0<p.y ∧ 0<p.z ∧ 3<p.y+p.z ∧ p∈S.D := by
        intro p hp;simp only [mem_insert,mem_singleton] at hp
        rcases hp with rfl | rfl | rfl <;> norm_num <;> assumption
      have hb:=t3_equal_height_resource_lower S hg hf he hh ht hk hy hz _ hB
      have ha:=yz_three_extra_area S ht _ _ _ (by decide) (by decide) (by decide) hB
      norm_num at hb
      omega
    · obtain ⟨h22,h13,h14⟩:=t3_missing31_standard_points S hg hf ht hy hz hY hZ hnot
      have hB : ∀ p∈({Point3.mk 0 2 2,Point3.mk 0 1 3,Point3.mk 0 1 4}:Finset Point3),
          p.x=0 ∧ 0<p.y ∧ 0<p.z ∧ 3<p.y+p.z ∧ p∈S.D := by
        intro p hp;simp only [mem_insert,mem_singleton] at hp
        rcases hp with rfl | rfl | rfl <;> norm_num <;> assumption
      have hb:=t3_equal_height_resource_lower S hg hf he hh ht hk hy hz _ hB
      have ha:=yz_three_extra_area S ht _ _ _ (by decide) (by decide) (by decide) hB
      norm_num at hb
      omega
  have hs : (pair12Count S.D+pair12Count S.D+5)^2≤4*S.m:=by nlinarith
  rw [fullTarget_eq_square,←he,ht]
  norm_num only [Nat.add_assoc] at *
  omega

end NSP3
