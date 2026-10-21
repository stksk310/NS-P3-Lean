import NSP3.SymbolicT3UnitPatterns

namespace NSP3
open Finset

private theorem rectangle23_lower (B C : ℕ) :
    B*C≤(ferrersRectangle 3 B C).card+3 := by
  classical
  let P:=(Icc 1 B).product (Icc 1 C)
  let Q:=P.filter (fun p=>¬3<p.1+p.2)
  have hsub : Q⊆{(1,1),(1,2),(2,1)} := by
    intro p hp
    obtain ⟨hp,hs⟩:=mem_filter.mp hp
    have h1:=mem_Icc.mp (mem_product.mp hp).1
    have h2:=mem_Icc.mp (mem_product.mp hp).2
    have he : (p.1=1 ∧ p.2=1) ∨ (p.1=1 ∧ p.2=2) ∨ (p.1=2 ∧ p.2=1):=by omega
    simpa only [mem_insert,mem_singleton,Prod.mk.injEq,Prod.ext_iff] using he
  have hq:=card_le_card hsub
  norm_num at hq
  have hsplit:=card_filter_add_card_filter_not (s:=P) (fun p=>3<p.1+p.2)
  have hp : P.card=B*C:=by simp [P]
  change (ferrersRectangle 3 B C).card+Q.card=P.card at hsplit
  omega

private theorem box_yz_weighted_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hy : 2≤g.y) (hz : 2≤g.z) (w : ℕ)
    (hw : 1+w≤ferrersPlaneDefect (pair12Count S.D) g.x g.y) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      3*pair12Count S.D+g.x*g.y*g.z+g.y*g.z+2+w≤S.m := by
  have hm:=fullSupport_symbolic_BW_lower S hg hf ho
  have hH:=positive_box_H_lower S g hf
  have hp:=Nat.mul_pos (Nat.mul_pos hf.1 hf.2.1) hf.2.2
  have hrect:=rectangle23_lower g.y g.z
  have hrectD : (ferrersRectangle 3 g.y g.z).card≤ferrersPlaneDefect 3 g.y g.z:=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h13 : 1≤ferrersPlaneDefect (pair13Count S.D) g.x g.z:=le_max_left _ _
  have hBC : 4≤g.y*g.z:=by nlinarith [Nat.mul_le_mul_right g.z hy]
  have hX:=le_max_left (pair12Count S.D) g.x
  have hY:=le_max_left (pair12Count S.D) g.y
  have hZ:=le_max_left (pair12Count S.D) g.z
  unfold fullSupportSymbolicBW at hm
  rw [ht] at hm
  have hc3 : Nat.choose 3 2=3:=by decide
  rw [hc3] at hm
  omega

/-- Positive box and actual yz rectangle are disjoint support resources. -/
theorem fullSupport_t3_positive_box_yz_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hy : 2≤g.y) (hz : 2≤g.z) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      3*pair12Count S.D+g.x*g.y*g.z+g.y*g.z+2≤S.m := by
  simpa only [Nat.add_zero] using
    box_yz_weighted_lower S hg hf ho ht hy hz 0 (le_max_left _ _)

private theorem W_near_last (r : ℕ) (hr : 4 ≤ r) :
    2*r-4≤ferrersW r (r-2) 2 := by
  have hi : r-2∈Icc (r-2) (r-2):=by simp
  have h:=single_le_sum (f:=fun i=>min ((r-2)*(r-i)) (2*i))
    (fun _ _=>Nat.zero_le _) hi
  unfold ferrersW
  have e : r-(r-2)=2:=by omega
  rw [e] at h
  have he : min ((r-2)*2) (2*(r-2))=2*r-4:=by omega
  rw [he] at h
  exact h

private theorem square_from_volume (r s V m : ℕ) (hs : 3 ≤ s) (ho : s ≤ r)
    (hm : Nat.choose r 2+Nat.choose s 2+3*r+V+2 ≤ m)
    (hv : 3*r+5≤V) : (r+s+5)^2≤4*m := by
  have cr : 2*Nat.choose r 2=r*(r-1):=by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1):=by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r:=by omega
  have es : s-1+1=s:=by omega
  have ed : r-s+s=r:=Nat.sub_add_cancel ho
  nlinarith only [cr,cs,er,es,ed,hm,hv,Nat.zero_le ((r-s)^2)]

/-- A uniform symbolic theorem for all nonunit coordinates and every r>=6. -/
theorem fullSupport_t3_no_unit_ge6_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : 6≤pair12Count S.D) (hx : 2≤g.x) (hy : 2≤g.y) (hz : 2≤g.z) :
    fullTarget S≤S.m := by
  let r:=pair12Count S.D
  let s:=pair13Count S.D
  let A:=g.x
  let B:=g.y
  let C:=g.z
  have hs : 3 ≤ s:=by dsimp [s];have:=ho.1;omega
  have hsr : s≤r:=ho.2
  have hr6 : 6≤r:=hr
  have hA2 : 2≤A:=hx
  have hB2 : 2≤B:=hy
  have hC2 : 2≤C:=hz
  have hc : r+2≤A+B+C:=pair12_terminal_return_capacity_ordered S hg hf ho
  have hm : Nat.choose r 2+Nat.choose s 2+3*r+A*B*C+B*C+2≤S.m:=
    fullSupport_t3_positive_box_yz_lower S hg hf ho ht hy hz
  have hBC : 4≤B*C:=by nlinarith [Nat.mul_le_mul_right C hB2]
  have hsq : (r+s+5)^2≤4*S.m := by
    by_cases hAhi : r-1≤A
    · have hv0 : 4*(A+1)≤A*B*C+B*C := by
        calc
          _≤B*C*(A+1):=Nat.mul_le_mul_right (A+1) hBC
          _=A*B*C+B*C:=by ring
      exact square_from_volume r s (A*B*C+B*C) S.m hs hsr (by omega) (by omega)
    · by_cases hAmid : A≤r-3
      · let b:=B-2
        let c:=C-2
        have eb : B=b+2:=by dsimp [b];omega
        have ec : C=c+2:=by dsimp [c];omega
        have hc' : r-A≤b+c+2:=by omega
        have hBC' : 2*(r-A)≤B*C:=by
          rw [eb,ec]
          nlinarith only [hc',Nat.zero_le (b*c)]
        have hv0 : 2*(r-A)*(A+1)≤A*B*C+B*C := by
          calc
            _≤B*C*(A+1):=Nat.mul_le_mul_right (A+1) hBC'
            _=A*B*C+B*C:=by ring
        let a:=A-2
        let d:=r-3-A
        have ea : A=a+2:=by dsimp [a];omega
        have er2 : r-2=a+d+3:=by dsimp [a,d];omega
        have erA : r-A=d+3:=by dsimp [d];omega
        have hv1 : 3*(r-2)≤(r-A)*(A+1):=by
          rw [er2,erA,ea]
          nlinarith only [Nat.zero_le (a*d)]
        have hv2 : 6*(r-2)≤A*B*C+B*C:=by nlinarith only [hv0,hv1]
        exact square_from_volume r s (A*B*C+B*C) S.m hs hsr (by omega) (by omega)
      · have hAe : A=r-2:=by omega
        by_cases hBC6 : 6≤B*C
        · have hv0 : 6*(A+1)≤A*B*C+B*C := by
            calc
              _≤B*C*(A+1):=Nat.mul_le_mul_right (A+1) hBC6
              _=A*B*C+B*C:=by ring
          exact square_from_volume r s (A*B*C+B*C) S.m hs hsr (by omega) (by omega)
        · have hBe : B=2:=by nlinarith [Nat.mul_le_mul_left B hC2]
          have hCe : C=2:=by rw [hBe] at hBC6;omega
          have hW : 2*r-4≤ferrersPlaneDefect r A B:=by
            have h : 2*r-4≤ferrersW r A B:=by
              simpa only [hAe,hBe] using W_near_last r (by omega)
            exact le_trans h (le_trans (le_max_right _ _) (le_max_right _ _))
          have hW' : 1+(2*r-5)≤ferrersPlaneDefect (pair12Count S.D) g.x g.y:=by
            change 1+(2*r-5)≤ferrersPlaneDefect r A B
            omega
          have hm' :=box_yz_weighted_lower S hg hf ho ht hy hz (2*r-5) hW'
          change Nat.choose r 2+Nat.choose s 2+3*r+A*B*C+B*C+2+(2*r-5)≤S.m at hm'
          have hV : 3*r+5≤A*B*C+B*C+(2*r-5):=by rw [hAe,hBe,hCe];omega
          exact square_from_volume r s (A*B*C+B*C+(2*r-5)) S.m hs hsr (by omega) hV
  change (pair12Count S.D+pair13Count S.D+5)^2≤4*S.m at hsq
  rw [fullTarget_eq_square,ht]
  norm_num only [Nat.add_assoc] at *
  omega

end NSP3
