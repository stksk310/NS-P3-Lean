import NSP3.SymbolicFerrersArea
import NSP3.OrderedPairBoundaries
import NSP3.SymbolicFerrersRank

namespace NSP3.Ferrers13

/- These four definitions are definitionally the frozen obligation's formulas,
   in a separate namespace so the standalone frozen file remains unchanged. -/
noncomputable def cornerX (S : CyclicStaircase) (i : ℕ) : ℕ :=
  if hzero : i=0 then 0 else if hi : i ≤ pair13Count S.D then
    (orderedPair13Boundary S ⟨i-1, by omega⟩).val.x else pure1Intercept S
noncomputable def cornerY (S : CyclicStaircase) (i : ℕ) : ℕ :=
  if hzero : i=0 then pure3Intercept S else if hi : i ≤ pair13Count S.D then
    (orderedPair13Boundary S ⟨i-1, by omega⟩).val.z else 0
noncomputable def gapU (S : CyclicStaircase) (i : ℕ) : ℕ :=
  cornerX S (i+1)-cornerX S i-1
noncomputable def gapV (S : CyclicStaircase) (i : ℕ) : ℕ :=
  cornerY S i-cornerY S (i+1)-1

@[simp] theorem cornerX_zero (S : CyclicStaircase) : cornerX S 0 = 0 := by
  simp [cornerX]
@[simp] theorem cornerY_zero (S : CyclicStaircase) : cornerY S 0 = pure3Intercept S := by
  simp [cornerY]
@[simp] theorem cornerX_last (S : CyclicStaircase) :
    cornerX S (pair13Count S.D+1) = pure1Intercept S := by simp [cornerX]
@[simp] theorem cornerY_last (S : CyclicStaircase) :
    cornerY S (pair13Count S.D+1) = 0 := by simp [cornerY]

theorem cornerX_inner (S : CyclicStaircase) (i : Fin (pair13Count S.D)) :
    cornerX S (i.val+1) = (orderedPair13Boundary S i).val.x := by
  simp [cornerX, show i.val+1 ≤ pair13Count S.D from i.isLt]
theorem cornerY_inner (S : CyclicStaircase) (i : Fin (pair13Count S.D)) :
    cornerY S (i.val+1) = (orderedPair13Boundary S i).val.z := by
  simp [cornerY, show i.val+1 ≤ pair13Count S.D from i.isLt]

theorem boundary_lt_intercepts (S : CyclicStaircase) (b : Pair13Boundary S) :
    b.val.x < pure1Intercept S ∧ b.val.z < pure3Intercept S := by
  have hx : Point3.mk b.val.x 0 0 ∈ S.D := S.down_closed (b := b.val.pred3)
    ⟨le_rfl, Nat.zero_le _, Nat.zero_le _⟩ (b.property.1.pred3_mem b.property.2.2.2)
  have hy : Point3.mk 0 0 b.val.z ∈ S.D := S.down_closed (b := b.val.pred1)
    ⟨Nat.zero_le _, Nat.zero_le _, le_rfl⟩ (b.property.1.pred1_mem b.property.2.1)
  exact ⟨(pure1_axis_mem_iff S _).mp hx, (pure3_axis_mem_iff S _).mp hy⟩

theorem cornerX_lt (S : CyclicStaircase) {i j : ℕ}
    (hij : i < j) (hj : j ≤ pair13Count S.D+1) : cornerX S i < cornerX S j := by
  by_cases hi0 : i=0
  · subst i
    by_cases hjr : j ≤ pair13Count S.D
    · let k : Fin (pair13Count S.D) := ⟨j-1, by omega⟩
      have he : k.val+1=j := by dsimp [k]; omega
      rw [cornerX_zero, ← he, cornerX_inner]
      exact (orderedPair13Boundary S k).property.2.1
    · have hjlast : j=pair13Count S.D+1 := by omega
      rw [hjlast, cornerX_zero, cornerX_last]
      exact (pure1Intercept_pure S).1
  · have hir : i ≤ pair13Count S.D := by omega
    let a : Fin (pair13Count S.D) := ⟨i-1, by omega⟩
    have hea : a.val+1=i := by dsimp [a]; omega
    by_cases hjr : j ≤ pair13Count S.D
    · let b : Fin (pair13Count S.D) := ⟨j-1, by omega⟩
      have heb : b.val+1=j := by dsimp [b]; omega
      rw [← hea, ← heb, cornerX_inner, cornerX_inner]
      apply orderedPair13Boundary_x_strictMono S
      change a.val < b.val
      dsimp [a,b]; omega
    · have hjlast : j=pair13Count S.D+1 := by omega
      rw [← hea, cornerX_inner, hjlast, cornerX_last]
      exact (boundary_lt_intercepts S _).1

theorem cornerY_lt (S : CyclicStaircase) {i j : ℕ}
    (hij : i < j) (hj : j ≤ pair13Count S.D+1) : cornerY S j < cornerY S i := by
  by_cases hi0 : i=0
  · subst i
    by_cases hjr : j ≤ pair13Count S.D
    · let k : Fin (pair13Count S.D) := ⟨j-1, by omega⟩
      have he : k.val+1=j := by dsimp [k]; omega
      rw [cornerY_zero, ← he, cornerY_inner]
      exact (boundary_lt_intercepts S _).2
    · have hjlast : j=pair13Count S.D+1 := by omega
      rw [hjlast, cornerY_zero, cornerY_last]
      exact (pure3Intercept_pure S).2.2
  · have hir : i ≤ pair13Count S.D := by omega
    let a : Fin (pair13Count S.D) := ⟨i-1, by omega⟩
    have hea : a.val+1=i := by dsimp [a]; omega
    by_cases hjr : j ≤ pair13Count S.D
    · let b : Fin (pair13Count S.D) := ⟨j-1, by omega⟩
      have heb : b.val+1=j := by dsimp [b]; omega
      rw [← hea, ← heb, cornerY_inner, cornerY_inner]
      apply orderedPair13Boundary_z_strictAnti S
      change a.val < b.val
      dsimp [a,b]; omega
    · have hjlast : j=pair13Count S.D+1 := by omega
      rw [← hea, cornerY_inner, hjlast, cornerY_last]
      exact (orderedPair13Boundary S a).property.2.2.2

theorem cornerX_le (S : CyclicStaircase) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ pair13Count S.D+1) : cornerX S i ≤ cornerX S j := by
  rcases hij.eq_or_lt with h | h
  · subst i; rfl
  · exact (cornerX_lt S h hj).le
theorem cornerY_le (S : CyclicStaircase) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ pair13Count S.D+1) : cornerY S j ≤ cornerY S i := by
  rcases hij.eq_or_lt with h | h
  · subst i; rfl
  · exact (cornerY_lt S h hj).le

theorem orderedPair13Boundary_exhaustive (S : CyclicStaircase) (b : Pair13Boundary S) :
    ∃ k, orderedPair13Boundary S k = b :=
  (Fintype.orderIsoFinOfCardEq (Pair13Boundary S) (card_pair13Boundary S)).surjective b

/-- The semantic adapter: genuine corners determine every column of the full plane. -/
theorem pair13_strip_mem_iff (S : CyclicStaircase) {i x y : ℕ}
    (hi : i ≤ pair13Count S.D) (hx : cornerX S i ≤ x)
    (hx' : x < cornerX S (i+1)) : Point3.mk x 0 y ∈ S.D ↔ y < cornerY S i := by
  constructor
  · intro hm
    by_contra hnot
    have hy : cornerY S i ≤ y := by omega
    by_cases hi0 : i=0
    · subst i
      have hm' : Point3.mk 0 0 (pure3Intercept S) ∈ S.D :=
        S.down_closed (b := Point3.mk x 0 y)
          ⟨Nat.zero_le _, le_rfl, by simpa using hy⟩ hm
      exact (pure3Intercept_minimalComplement S).not_mem hm'
    · let a : Fin (pair13Count S.D) := ⟨i-1, by omega⟩
      have hea : a.val+1=i := by dsimp [a]; omega
      rw [← hea, cornerX_inner] at hx
      rw [← hea, cornerY_inner] at hy
      exact (orderedPair13Boundary S a).property.1.not_mem
        (S.down_closed ⟨hx,by simp [(orderedPair13Boundary S a).property.2.2.1],hy⟩ hm)
  · intro hy
    by_contra hm
    obtain ⟨b,hb,hble⟩ := exists_minimalComplement_le hm
    have hbz : b.y=0 := by have := hble.2.1; change b.y ≤ 0 at this; omega
    have hbx : b.x ≤ x := hble.1
    have hby : b.z ≤ y := hble.2.2
    have hxX : x < pure1Intercept S :=
      lt_of_lt_of_le hx' (by simpa using cornerX_le S (show i+1 ≤ pair13Count S.D+1 by omega) le_rfl)
    have hyY : y < pure3Intercept S :=
      lt_of_lt_of_le hy (by simpa using cornerY_le S (Nat.zero_le i) (by omega))
    by_cases hbx0 : b.x=0
    · have haxis : Point3.mk 0 0 b.z ∈ S.D := (pure3_axis_mem_iff S _).mpr (by omega)
      have he : b=Point3.mk 0 0 b.z := by ext <;> simp [hbx0,hbz]
      exact hb.not_mem (he ▸ haxis)
    · by_cases hby0 : b.z=0
      · have haxis : Point3.mk b.x 0 0 ∈ S.D := (pure1_axis_mem_iff S _).mpr (by omega)
        have he : b=Point3.mk b.x 0 0 := by ext <;> simp [hby0,hbz]
        exact hb.not_mem (he ▸ haxis)
      · let bb : Pair13Boundary S := ⟨b,hb,by exact ⟨by omega,hbz,by omega⟩⟩
        obtain ⟨k,hk⟩ := orderedPair13Boundary_exhaustive S bb
        have hkx : cornerX S (k.val+1)=b.x := by rw [cornerX_inner,hk]
        have hky : cornerY S (k.val+1)=b.z := by rw [cornerY_inner,hk]
        by_cases hki : k.val+1 ≤ i
        · have hle := cornerY_le S hki (by omega)
          rw [hky] at hle
          omega
        · have hle := cornerX_le S (show i+1 ≤ k.val+1 by omega) (by omega)
          rw [hkx] at hle
          omega

noncomputable def strip (S : CyclicStaircase) (i : ℕ) : Finset Point3 := by
  classical
  exact ((Finset.Ico (cornerX S i) (cornerX S (i+1))).product
    (Finset.range (cornerY S i))).image (fun p => Point3.mk p.1 0 p.2)

@[simp] theorem mem_strip (S : CyclicStaircase) (i : ℕ) (p : Point3) :
    p ∈ strip S i ↔ cornerX S i ≤ p.x ∧ p.x < cornerX S (i+1) ∧
      p.z < cornerY S i ∧ p.y=0 := by
  classical
  simp only [strip, Finset.mem_image]
  constructor
  · rintro ⟨⟨x,y⟩,h,rfl⟩
    have h' := Finset.mem_product.mp h
    exact ⟨(Finset.mem_Ico.mp h'.1).1,(Finset.mem_Ico.mp h'.1).2,
      Finset.mem_range.mp h'.2,rfl⟩
  · rintro ⟨hl,hu,hy,hz⟩
    exact ⟨(p.x,p.z),Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨hl,hu⟩,Finset.mem_range.mpr hy⟩,by ext <;> simp [hz]⟩

theorem strip_card (S : CyclicStaircase) (i : ℕ) :
    (strip S i).card = (cornerX S (i+1)-cornerX S i)*cornerY S i := by
  classical
  rw [strip,Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ h
    exact Prod.ext (congrArg Point3.x h) (congrArg Point3.z h)

theorem strips_disjoint (S : CyclicStaircase) {i j : ℕ}
    (hi : i ≤ pair13Count S.D) (hj : j ≤ pair13Count S.D) (hne : i≠j) :
    Disjoint (strip S i) (strip S j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := (mem_strip S i p).mp hp
  have hq' := (mem_strip S j p).mp hq
  rcases lt_or_gt_of_ne hne with h | h
  · have := cornerX_le S (show i+1 ≤ j by omega) (by omega)
    omega
  · have := cornerX_le S (show j+1 ≤ i by omega) (by omega)
    omega

theorem full_plane_eq_strips (S : CyclicStaircase) :
    pair13PlaneSection S.D = (Finset.range (pair13Count S.D+1)).biUnion (strip S) := by
  classical
  ext p
  simp only [pair13PlaneSection,Finset.mem_filter,Finset.mem_biUnion,Finset.mem_range]
  constructor
  · rintro ⟨hp,hz⟩
    have hx : p.x < pure1Intercept S := (pure1_axis_mem_iff S _).mp
      (S.down_closed (b := p) ⟨le_rfl,Nat.zero_le _,Nat.zero_le _⟩ hp)
    have hx' : p.x < cornerX S (pair13Count S.D+1) := by simpa using hx
    obtain ⟨i,hi,hl,hu⟩ := Ferrers.exists_strip_index (cornerX_zero S) hx'
    refine ⟨i,hi,(mem_strip S i p).mpr ⟨hl,hu,?_,hz⟩⟩
    have he : Point3.mk p.x 0 p.z=p := by ext <;> simp [hz]
    exact (pair13_strip_mem_iff S (by omega) hl hu).mp (he ▸ hp)
  · rintro ⟨i,hi,hp⟩
    obtain ⟨hl,hu,hy,hz⟩ := (mem_strip S i p).mp hp
    have he : Point3.mk p.x 0 p.z=p := by ext <;> simp [hz]
    exact ⟨he ▸ (pair13_strip_mem_iff S (by omega) hl hu).mpr hy,hz⟩

/-- Exact full-plane cardinality, including both pure axes and the origin. -/
theorem pair13_full_plane_card (S : CyclicStaircase) :
    (pair13PlaneSection S.D).card =
      (Finset.range (pair13Count S.D+1)).sum
        (fun i => (cornerX S (i+1)-cornerX S i)*cornerY S i) := by
  classical
  rw [full_plane_eq_strips,Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun i _ => strip_card S i)
  · intro i hi j hj hne
    exact strips_disjoint S (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hne

/-- Remove the disjoint y-axis (including origin) and positive x-axis. -/
theorem pair13_remove_axes (S : CyclicStaircase) :
    (plane13PosFinset S).card+pure1Intercept S+pure3Intercept S =
      (pair13PlaneSection S.D).card+1 := by
  classical
  let P := pair13PlaneSection S.D
  let Q := P.filter (fun p => p.x ≠ 0)
  have hpart1 := Finset.card_filter_add_card_filter_not (s := P) (fun p => p.x=0)
  have hpart2 := Finset.card_filter_add_card_filter_not (s := Q) (fun p => p.z=0)
  have hyaxis : P.filter (fun p => p.x=0) =
      (Finset.range (pure3Intercept S)).image (fun y => Point3.mk 0 0 y) := by
    ext p
    simp only [P,pair13PlaneSection,Finset.mem_filter,Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨⟨hp,hz⟩,hx⟩
      have he : Point3.mk 0 0 p.z=p := by ext <;> simp [hx,hz]
      exact ⟨p.z,(pure3_axis_mem_iff S _).mp (he ▸ hp),he⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨(pure3_axis_mem_iff S y).mpr hy,rfl⟩,rfl⟩
  have hxaxis : Q.filter (fun p => p.z=0) =
      (Finset.Ico 1 (pure1Intercept S)).image (fun x => Point3.mk x 0 0) := by
    ext p
    simp only [Q,P,pair13PlaneSection,Finset.mem_filter,Finset.mem_image,Finset.mem_Ico]
    constructor
    · rintro ⟨⟨⟨hp,hz⟩,hx⟩,hy⟩
      have he : Point3.mk p.x 0 0=p := by ext <;> simp [hy,hz]
      exact ⟨p.x,⟨by omega,(pure1_axis_mem_iff S _).mp (he ▸ hp)⟩,he⟩
    · rintro ⟨x,⟨hx,hX⟩,rfl⟩
      exact ⟨⟨⟨(pure1_axis_mem_iff S x).mpr hX,rfl⟩,by simpa using (show x≠0 by omega)⟩,rfl⟩
  have hpositive : Q.filter (fun p => ¬p.z=0) = plane13PosFinset S := by
    ext p
    simp only [Q,P,pair13PlaneSection,Finset.mem_filter,mem_plane13PosFinset]
    constructor
    · rintro ⟨⟨⟨hp,hz⟩,hx⟩,hy⟩
      exact ⟨hp,by omega,hz,by omega⟩
    · rintro ⟨hp,hx,hz,hy⟩
      exact ⟨⟨⟨hp,hz⟩,by omega⟩,by omega⟩
  have hycard : (P.filter (fun p => p.x=0)).card=pure3Intercept S := by
    rw [hyaxis,Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ h; exact congrArg Point3.z h
  have hxcard : (Q.filter (fun p => p.z=0)).card=pure1Intercept S-1 := by
    rw [hxaxis,Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ h; exact congrArg Point3.x h
  rw [hycard] at hpart1
  rw [hxcard,hpositive] at hpart2
  change pure3Intercept S+Q.card=P.card at hpart1
  have hX : 0 < pure1Intercept S := (pure1Intercept_pure S).1
  change (plane13PosFinset S).card+pure1Intercept S+pure3Intercept S = P.card+1
  omega

theorem gapU_step (S : CyclicStaircase) {i : ℕ} (hi : i ≤ pair13Count S.D) :
    cornerX S (i+1) = cornerX S i + 1 + gapU S i := by
  have := cornerX_lt S (show i < i+1 by omega) (by omega)
  unfold gapU
  omega

theorem gapV_step (S : CyclicStaircase) {i : ℕ} (hi : i ≤ pair13Count S.D) :
    cornerY S i = cornerY S (i+1) + 1 + gapV S i := by
  have := cornerY_lt S (show i < i+1 by omega) (by omega)
  unfold gapV
  omega

theorem gapU_prefix (S : CyclicStaircase) {k : ℕ} (hk : k ≤ pair13Count S.D+1) :
    (Finset.range k).sum (gapU S)+k = cornerX S k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (by omega)
    have hstep := gapU_step S (i := k) (by omega)
    rw [Finset.sum_range_succ]
    change (Finset.range k).sum (gapU S)+gapU S k+(k+1)=cornerX S (k+1)
    omega

theorem gapV_prefix (S : CyclicStaircase) {k : ℕ} (hk : k ≤ pair13Count S.D+1) :
    (Finset.range k).sum (gapV S)+k+cornerY S k = pure3Intercept S := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (by omega)
    have hstep := gapV_step S (i := k) (by omega)
    rw [Finset.sum_range_succ]
    change (Finset.range k).sum (gapV S)+gapV S k+(k+1)+cornerY S (k+1)=pure3Intercept S
    omega

end NSP3.Ferrers13


