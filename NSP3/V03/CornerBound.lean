import NSP3.V03.CornerLayers

/-!
Boundary-weight bookkeeping for the unconditional three-dimensional corner
inequality.  Each nonexcluded boundary corner is used once, and a full
support corner may be used twice.  The pure y and pure z corners are unused.
-/
namespace NSP3.V03
open Finset

set_option maxHeartbeats 4000000

noncomputable def fullSupportCorners (D : Finset Point3) : Finset Point3 := by
  classical
  exact (cornerBoundary D).filter FullSupport

@[simp] theorem mem_fullSupportCorners (D : Finset Point3) (b : Point3) :
    b∈fullSupportCorners D ↔ MinimalComplement D b ∧ FullSupport b := by
  classical
  simp [fullSupportCorners]

noncomputable def globalOrientedCorners (D : Finset Point3) : Finset (Point3×Bool) := by
  classical
  exact ((cornerBoundary D).product univ).filter (fun v =>
    if v.2 then 0<v.1.y ∧ 0<v.1.z else 0<v.1.x)

@[simp] theorem mem_globalOrientedCorners (D : Finset Point3) (b : Point3) (i : Bool) :
    (b,i)∈globalOrientedCorners D ↔ MinimalComplement D b ∧
      (if i then 0<b.y ∧ 0<b.z else 0<b.x) := by
  classical
  simp [globalOrientedCorners]

theorem minimalComplement_slice_zero_iff (D : Finset Point3) {b : Point3}
    (hbz : b.z=0) :
    MinimalComplement (cornerSlice D 0) b ↔ MinimalComplement D b := by
  have heq : liftPoint 0 b=b := by ext <;> simp [liftPoint,hbz]
  have hp1 : liftPoint 0 b.pred1=b.pred1 := by ext <;> simp [liftPoint,hbz]
  have hp2 : liftPoint 0 b.pred2=b.pred2 := by ext <;> simp [liftPoint,hbz]
  constructor
  · intro hb
    refine ⟨?_,?_,?_,?_⟩
    · intro h
      exact hb.not_mem ((mem_cornerSlice _ _ _).mpr ⟨hbz,heq.symm ▸ h⟩)
    · intro hx
      have h := ((mem_cornerSlice _ _ _).mp (hb.pred1_mem hx)).2
      rwa [hp1] at h
    · intro hy
      have h := ((mem_cornerSlice _ _ _).mp (hb.pred2_mem hy)).2
      rwa [hp2] at h
    · intro hz; omega
  · intro hb
    refine ⟨?_,?_,?_,?_⟩
    · intro h
      have h' := ((mem_cornerSlice _ _ _).mp h).2
      rw [heq] at h'
      exact hb.not_mem h'
    · intro hx
      exact (mem_cornerSlice _ _ _).mpr ⟨by simp [hbz],hp1.symm ▸ hb.pred1_mem hx⟩
    · intro hy
      exact (mem_cornerSlice _ _ _).mpr ⟨by simp [hbz],hp2.symm ▸ hb.pred2_mem hy⟩
    · intro hz; omega

theorem minimalComplement_slice_step_iff (D : Finset Point3) (z : ℕ) {b : Point3}
    (hbz : b.z=0) :
    (MinimalComplement (cornerSlice D (z+1)) b ∧ b∈cornerSlice D z) ↔
      MinimalComplement D (liftPoint (z+1) b) := by
  have hp1 : liftPoint (z+1) b.pred1=(liftPoint (z+1) b).pred1 := rfl
  have hp2 : liftPoint (z+1) b.pred2=(liftPoint (z+1) b).pred2 := rfl
  have hp3 : liftPoint z b=(liftPoint (z+1) b).pred3 := by
    ext <;> simp [liftPoint,Point3.pred3]
  constructor
  · rintro ⟨hb,he⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro h
      exact hb.not_mem ((mem_cornerSlice _ _ _).mpr ⟨hbz,h⟩)
    · intro hx
      have h := ((mem_cornerSlice _ _ _).mp (hb.pred1_mem hx)).2
      rwa [hp1] at h
    · intro hy
      have h := ((mem_cornerSlice _ _ _).mp (hb.pred2_mem hy)).2
      rwa [hp2] at h
    · intro _
      have h := ((mem_cornerSlice _ _ _).mp he).2
      rwa [hp3] at h
  · intro hb
    refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
    · intro h
      exact hb.not_mem (((mem_cornerSlice _ _ _).mp h).2)
    · intro hx
      apply (mem_cornerSlice _ _ _).mpr
      exact ⟨by simp [hbz],hp1.symm ▸ hb.pred1_mem hx⟩
    · intro hy
      apply (mem_cornerSlice _ _ _).mpr
      exact ⟨by simp [hbz],hp2.symm ▸ hb.pred2_mem hy⟩
    · intro hz; omega
    · apply (mem_cornerSlice _ _ _).mpr
      exact ⟨hbz,hp3.symm ▸ hb.pred3_mem (by simp [liftPoint])⟩

theorem oriented_slice_card (D : Finset Point3) (z : ℕ) :
    (orientedCorners (cornerSlice D z) (cornerSlice D (z+1))).card =
      ((globalOrientedCorners D).filter (fun v => v.1.z=z+1)).card := by
  classical
  apply card_bij (fun v _ => (liftPoint (z+1) v.1,v.2))
  · rintro ⟨b,i⟩ hv
    obtain ⟨hb,he,hi⟩ := (mem_orientedCorners _ _ b i).mp hv
    have hbz := ((mem_cornerSlice _ _ _).mp he).1
    apply mem_filter.mpr
    refine ⟨(mem_globalOrientedCorners _ _ _).mpr ⟨?_,?_⟩,rfl⟩
    · exact (minimalComplement_slice_step_iff D z hbz).mp ⟨hb,he⟩
    · cases i <;> simpa [liftPoint] using hi
  · rintro ⟨b,i⟩ hb ⟨c,j⟩ hc heq
    obtain ⟨_,hbE,_⟩ := (mem_orientedCorners _ _ b i).mp hb
    obtain ⟨_,hcE,_⟩ := (mem_orientedCorners _ _ c j).mp hc
    have hbz := ((mem_cornerSlice _ _ _).mp hbE).1
    have hcz := ((mem_cornerSlice _ _ _).mp hcE).1
    have he := congrArg Prod.fst heq
    have hx := congrArg Point3.x he
    have hy := congrArg Point3.y he
    have hij : i=j := congrArg (fun v : Point3×Bool => v.2) heq
    apply Prod.ext
    · ext <;> simp_all [liftPoint]
    · exact hij
  · rintro ⟨b,i⟩ hv
    obtain ⟨hv,hbz⟩ := mem_filter.mp hv
    change b.z=z+1 at hbz
    obtain ⟨hb,hi⟩ := (mem_globalOrientedCorners D b i).mp hv
    have hflat : (flatPoint b).z=0 := rfl
    have hlift : liftPoint (z+1) (flatPoint b)=b := by
      ext <;> simp [liftPoint,flatPoint,hbz]
    have hback := (minimalComplement_slice_step_iff D z hflat).mpr (hlift.symm ▸ hb)
    refine ⟨(flatPoint b,i),(mem_orientedCorners _ _ _ _).mpr ⟨hback.1,hback.2,?_⟩,?_⟩
    · cases i <;> simpa [flatPoint,hbz] using hi
    · exact Prod.ext hlift rfl

theorem base_slice_corner_card (D : Finset Point3) :
    ((cornerBoundary (cornerSlice D 0)).filter (fun b => b.z=0 ∧ 0<b.x)).card =
      ((globalOrientedCorners D).filter (fun v => v.1.z=0)).card := by
  classical
  apply card_bij (fun b _ => (b,false))
  · intro b hb
    obtain ⟨hb,hbz,hbx⟩ := mem_filter.mp hb
    apply mem_filter.mpr
    refine ⟨(mem_globalOrientedCorners _ _ _).mpr ⟨?_,by simpa using hbx⟩,hbz⟩
    exact (minimalComplement_slice_zero_iff D hbz).mp ((mem_cornerBoundary _ _).mp hb)
  · intro b _ c _ heq
    exact congrArg Prod.fst heq
  · rintro ⟨b,i⟩ hv
    obtain ⟨hv,hbz⟩ := mem_filter.mp hv
    change b.z=0 at hbz
    obtain ⟨hb,hi⟩ := (mem_globalOrientedCorners D b i).mp hv
    cases i with
    | false =>
        refine ⟨b,mem_filter.mpr ⟨(mem_cornerBoundary _ _).mpr ?_,hbz,by simpa using hi⟩,rfl⟩
        exact (minimalComplement_slice_zero_iff D hbz).mpr hb
    | true => simp [hbz] at hi

theorem boundary_height_le {D : Finset Point3} {b : Point3}
    (hb : MinimalComplement D b) : b.z≤D.sup Point3.z+1 := by
  by_cases hz : 0<b.z
  · have h := le_sup (f := Point3.z) (hb.pred3_mem hz)
    change b.z-1≤D.sup Point3.z at h
    omega
  · omega

private theorem sum_range_shift (N : ℕ) (f : ℕ→ℕ) :
    f 0+∑ z∈range N,f (z+1)=∑ z∈range (N+1),f z := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,sum_range_succ]
    omega

/-- All counted layer resources are exactly the global oriented boundary. -/
theorem globalOriented_card_eq_layers (D : Finset Point3) :
    (globalOrientedCorners D).card =
      ((cornerBoundary (cornerSlice D 0)).filter (fun b => b.z=0 ∧ 0<b.x)).card+
      ∑ z∈range (D.sup Point3.z+1),
        (orientedCorners (cornerSlice D z) (cornerSlice D (z+1))).card := by
  classical
  have hfiber := card_eq_sum_card_fiberwise (s := globalOrientedCorners D)
    (f := fun v => v.1.z) (t := range (D.sup Point3.z+1+1)) (by
      intro v hv
      obtain ⟨hb,_⟩ := (mem_globalOrientedCorners _ _ _).mp hv
      apply mem_range.mpr
      have h := boundary_height_le hb
      change v.1.z<D.sup Point3.z+1+1
      omega)
  rw [hfiber,base_slice_corner_card]
  simp_rw [oriented_slice_card]
  exact (sum_range_shift (D.sup Point3.z+1)
    (fun z => ((globalOrientedCorners D).filter (fun v => v.1.z=z)).card)).symm

theorem maximal_card_le_globalOriented {D : Finset Point3} (hd : IsDownset D) :
    (maximalPoints D).card≤(globalOrientedCorners D).card := by
  rw [globalOriented_card_eq_layers]
  exact maximal_card_le_oriented_layers hd

private theorem bool_filter_card (B : Finset Point3) (P Q : Point3→Prop)
    [DecidablePred P] [DecidablePred Q] :
    ((B.product (univ : Finset Bool)).filter (fun v => if v.2 then Q v.1 else P v.1)).card =
      (B.filter P).card+(B.filter Q).card := by
  classical
  let fx : Point3→Point3×Bool := fun b => (b,false)
  let fy : Point3→Point3×Bool := fun b => (b,true)
  have hx : Function.Injective fx := fun _ _ h => congrArg Prod.fst h
  have hy : Function.Injective fy := fun _ _ h => congrArg Prod.fst h
  have heq : ((B.product univ).filter (fun v => if v.2 then Q v.1 else P v.1)) =
      (B.filter P).image fx ∪ (B.filter Q).image fy := by
    ext ⟨b,i⟩
    cases i <;> simp [fx,fy]
  have hdj : Disjoint ((B.filter P).image fx) ((B.filter Q).image fy) := by
    apply disjoint_left.mpr
    intro v hx hy
    obtain ⟨x,_,rfl⟩ := mem_image.mp hx
    obtain ⟨y,_,he⟩ := mem_image.mp hy
    have ht := congrArg Prod.snd he
    simp [fx,fy] at ht
  rw [heq,card_union_of_disjoint hdj,card_image_of_injective _ hx,card_image_of_injective _ hy]

theorem globalOriented_card_eq_weights (D : Finset Point3) :
    (globalOrientedCorners D).card =
      ((cornerBoundary D).filter (fun b => 0<b.x)).card+
      ((cornerBoundary D).filter (fun b => 0<b.y ∧ 0<b.z)).card := by
  classical
  simpa [globalOrientedCorners] using
    (bool_filter_card (cornerBoundary D) (fun b => 0<b.x) (fun b => 0<b.y ∧ 0<b.z))

private theorem zero_mem_of_nonempty {D : Finset Point3}
    (hd : IsDownset D) (hne : D.Nonempty) : Point3.zero∈D := by
  obtain ⟨p,hp⟩ := hne
  exact hd ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩ hp

theorem exists_pure_y_corner {D : Finset Point3}
    (hd : IsDownset D) (hne : D.Nonempty) :
    ∃ b,MinimalComplement D b ∧ b.x=0 ∧ 0<b.y ∧ b.z=0 := by
  let q : Point3 := ⟨0,D.sup Point3.y+1,0⟩
  have hq : q∉D := by
    intro h
    have h' := le_sup (f := Point3.y) h
    change D.sup Point3.y+1≤D.sup Point3.y at h'
    omega
  obtain ⟨b,hb,hle⟩ := exists_minimalComplement_le hq
  have hx : b.x=0 := by have := hle.1; dsimp [q] at this; omega
  have hz : b.z=0 := by have := hle.2.2; dsimp [q] at this; omega
  have hy : 0<b.y := by
    by_contra h
    have heq : b=Point3.zero := by ext <;> simp_all
    exact hb.not_mem (heq.symm ▸ zero_mem_of_nonempty hd hne)
  exact ⟨b,hb,hx,hy,hz⟩

theorem exists_pure_z_corner {D : Finset Point3}
    (hd : IsDownset D) (hne : D.Nonempty) :
    ∃ b,MinimalComplement D b ∧ b.x=0 ∧ b.y=0 ∧ 0<b.z := by
  let q : Point3 := ⟨0,0,D.sup Point3.z+1⟩
  have hq : q∉D := by
    intro h
    have h' := le_sup (f := Point3.z) h
    change D.sup Point3.z+1≤D.sup Point3.z at h'
    omega
  obtain ⟨b,hb,hle⟩ := exists_minimalComplement_le hq
  have hx : b.x=0 := by have := hle.1; dsimp [q] at this; omega
  have hy : b.y=0 := by have := hle.2.1; dsimp [q] at this; omega
  have hz : 0<b.z := by
    by_contra h
    have heq : b=Point3.zero := by ext <;> simp_all
    exact hb.not_mem (heq.symm ▸ zero_mem_of_nonempty hd hne)
  exact ⟨b,hb,hx,hy,hz⟩

/-- Pure y and pure z corners are unused; only full corners are counted twice. -/
theorem oriented_weight_bound {D : Finset Point3}
    (hd : IsDownset D) (hne : D.Nonempty) :
    (globalOrientedCorners D).card+2≤
      (cornerBoundary D).card+(fullSupportCorners D).card := by
  classical
  let B := cornerBoundary D
  let X := B.filter (fun b => 0<b.x)
  let Y := B.filter (fun b => 0<b.y ∧ 0<b.z)
  have hg : (globalOrientedCorners D).card=X.card+Y.card := globalOriented_card_eq_weights D
  have hi : X∩Y=fullSupportCorners D := by
    ext b
    simp [X,Y,B,fullSupportCorners,FullSupport,and_assoc]
    tauto
  have hc := card_union_add_card_inter X Y
  rw [hi] at hc
  obtain ⟨u,hu,hux,huy,huz⟩ := exists_pure_y_corner hd hne
  obtain ⟨v,hv,hvx,hvy,hvz⟩ := exists_pure_z_corner hd hne
  have huv : u≠v := by intro h; have he := congrArg Point3.y h; omega
  have huB : u∈B := (mem_cornerBoundary D u).mpr hu
  have hvB : v∈B := (mem_cornerBoundary D v).mpr hv
  have huU : u∉X∪Y := by simp [X,Y,hux,huz]
  have hvU : v∉X∪Y := by simp [X,Y,hvx,hvy]
  have hsub : insert u (insert v (X∪Y))⊆B := by
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact huB
    rcases mem_insert.mp hb with rfl | hb
    · exact hvB
    rcases mem_union.mp hb with hx | hy
    · exact (mem_filter.mp hx).1
    · exact (mem_filter.mp hy).1
  have hs := card_le_card hsub
  rw [card_insert_of_notMem (by simp [huv,huU]),card_insert_of_notMem hvU] at hs
  change (globalOrientedCorners D).card+2≤B.card+(fullSupportCorners D).card
  omega

/-- Unconditional finite-downset corner bound; no homological certificate premise. -/
theorem maximalPoints_card_add_two_le_boundary {D : Finset Point3}
    (hd : IsDownset D) (hne : D.Nonempty) :
    (maximalPoints D).card+2≤
      (cornerBoundary D).card+(fullSupportCorners D).card := by
  have hm := maximal_card_le_globalOriented hd
  have hb := oriented_weight_bound hd hne
  omega

theorem maximalPoints_card_add_two_le_boundary_natCard {D : Finset Point3}
    (hd : IsDownset D) (hne : D.Nonempty) :
    (maximalPoints D).card+2≤Nat.card {b : Point3 // MinimalComplement D b}+
      Nat.card {b : Point3 // MinimalComplement D b ∧ FullSupport b} := by
  classical
  have hb := maximalPoints_card_add_two_le_boundary hd hne
  have hcard : Nat.card {b : Point3 // MinimalComplement D b}=(cornerBoundary D).card :=
    Nat.subtype_card _ (mem_cornerBoundary D)
  have hfull : Nat.card {b : Point3 // MinimalComplement D b ∧ FullSupport b}=
      (fullSupportCorners D).card :=
    Nat.subtype_card _ (by intro b; simp)
  rw [hcard,hfull]
  exact hb

end NSP3.V03
