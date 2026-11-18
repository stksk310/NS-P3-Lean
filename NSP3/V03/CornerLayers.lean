import NSP3.V03.CornerPlanar

namespace NSP3.V03
open Finset

set_option maxHeartbeats 2000000

def flatPoint (p : Point3) : Point3 := ⟨p.x,p.y,0⟩
def liftPoint (z : ℕ) (p : Point3) : Point3 := ⟨p.x,p.y,z⟩

def cornerSlice (D : Finset Point3) (z : ℕ) : Finset Point3 :=
  (D.filter (fun p => p.z=z)).image flatPoint

@[simp] theorem mem_cornerSlice (D : Finset Point3) (z : ℕ) (p : Point3) :
    p∈cornerSlice D z ↔ p.z=0 ∧ liftPoint z p∈D := by
  constructor
  · intro hp
    obtain ⟨q,hq,hqp⟩ := mem_image.mp hp
    obtain ⟨hq,hqz⟩ := mem_filter.mp hq
    subst p
    refine ⟨rfl,?_⟩
    have he : liftPoint z (flatPoint q)=q := by ext <;> simp [liftPoint,flatPoint,hqz]
    rwa [he]
  · rintro ⟨hpz,hp⟩
    refine mem_image.mpr ⟨liftPoint z p,mem_filter.mpr ⟨hp,rfl⟩,?_⟩
    ext <;> simp [liftPoint,flatPoint,hpz]

theorem cornerSlice_planar (D : Finset Point3) (z : ℕ) : Planar (cornerSlice D z) :=
  fun p hp => (mem_cornerSlice D z p).mp hp |>.1

theorem cornerSlice_downset {D : Finset Point3} (hd : IsDownset D) (z : ℕ) :
    IsDownset (cornerSlice D z) := by
  intro p q hpq hq
  obtain ⟨hqz,hq⟩ := (mem_cornerSlice D z q).mp hq
  apply (mem_cornerSlice D z p).mpr
  refine ⟨by have := hpq.2.2; omega, hd ?_ hq⟩
  exact ⟨hpq.1,hpq.2.1,le_rfl⟩

theorem cornerSlice_antitone {D : Finset Point3} (hd : IsDownset D)
    {i j : ℕ} (hij : i≤j) : cornerSlice D j⊆cornerSlice D i := by
  intro p hp
  obtain ⟨hpz,hp⟩ := (mem_cornerSlice D j p).mp hp
  exact (mem_cornerSlice D i p).mpr
    ⟨hpz,hd (a := liftPoint i p) (b := liftPoint j p) ⟨le_rfl,le_rfl,hij⟩ hp⟩

theorem maximal_mem_of_smaller_set {E F : Finset Point3} (hFE : F⊆E)
    {p : Point3} (hp : p∈maximalPoints E) (hpF : p∈F) : p∈maximalPoints F := by
  obtain ⟨_,hmax⟩ := (mem_maximalPoints E p).mp hp
  exact (mem_maximalPoints F p).mpr ⟨hpF,fun q hq hpq => hmax q (hFE hq) hpq⟩

/-- Finite births and deaths telescope without subtraction or monotonicity hypotheses. -/
theorem layer_birth_death_balance {α : Type*} [DecidableEq α]
    (M : ℕ→Finset α) (N : ℕ) :
    (∑ i∈range N,(M i\M (i+1)).card)+(M N).card =
      (M 0).card+∑ i∈range N,(M (i+1)\M i).card := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,sum_range_succ]
    have h₁ := card_sdiff_add_card_inter (M N) (M (N+1))
    have h₂ := card_sdiff_add_card_inter (M (N+1)) (M N)
    rw [inter_comm] at h₂
    omega

theorem maximal_slice_iff {D : Finset Point3} (hd : IsDownset D) (p : Point3) :
    p∈maximalPoints D ↔ flatPoint p∈maximalPoints (cornerSlice D p.z) ∧
      flatPoint p∉cornerSlice D (p.z+1) := by
  constructor
  · intro hp
    obtain ⟨hp,hmax⟩ := (mem_maximalPoints D p).mp hp
    have hflat : flatPoint p∈cornerSlice D p.z := by
      apply (mem_cornerSlice _ _ _).mpr
      exact ⟨rfl,by simpa [liftPoint,flatPoint] using hp⟩
    refine ⟨(mem_maximalPoints _ _).mpr ⟨hflat,?_⟩,?_⟩
    · intro q hq hpq
      obtain ⟨hqz,hqD⟩ := (mem_cornerSlice _ _ _).mp hq
      have he := hmax (liftPoint p.z q) hqD ⟨hpq.1,hpq.2.1,le_rfl⟩
      have hx := congrArg Point3.x he
      have hy := congrArg Point3.y he
      change q.x=p.x at hx
      change q.y=p.y at hy
      exact Point3.ext hx hy hqz
    · intro hnext
      have hnextD := ((mem_cornerSlice _ _ _).mp hnext).2
      have he := hmax (liftPoint (p.z+1) (flatPoint p)) hnextD
        ⟨le_rfl,le_rfl,by change p.z≤p.z+1; omega⟩
      have hz := congrArg Point3.z he
      simp [liftPoint] at hz
  · rintro ⟨hmax,hnext⟩
    obtain ⟨hflat,hmax⟩ := (mem_maximalPoints _ _).mp hmax
    have hp : p∈D := by
      have h := ((mem_cornerSlice _ _ _).mp hflat).2
      simpa [liftPoint,flatPoint] using h
    apply (mem_maximalPoints D p).mpr
    refine ⟨hp,?_⟩
    intro q hq hpq
    have hqflat : flatPoint q∈cornerSlice D p.z := by
      apply (mem_cornerSlice _ _ _).mpr
      exact ⟨rfl,hd (a := liftPoint p.z (flatPoint q)) (b := q)
        ⟨le_rfl,le_rfl,hpq.2.2⟩ hq⟩
    have he := hmax (flatPoint q) hqflat ⟨hpq.1,hpq.2.1,le_rfl⟩
    have hx := congrArg Point3.x he
    have hy := congrArg Point3.y he
    change q.x=p.x at hx
    change q.y=p.y at hy
    have hz : q.z=p.z := by
      by_contra hn
      apply hnext
      apply (mem_cornerSlice _ _ _).mpr
      refine ⟨rfl,hd ?_ hq⟩
      change p.x≤q.x ∧ p.y≤q.y ∧ p.z+1≤q.z
      have hle : p.z≤q.z := hpq.2.2
      exact ⟨hpq.1,hpq.2.1,by omega⟩
    exact Point3.ext hx hy hz

/-- At a fixed height, 3D maxima are precisely the deaths of planar maxima. -/
theorem maximal_slice_image {D : Finset Point3} (hd : IsDownset D) (z : ℕ) :
    ((maximalPoints D).filter (fun p => p.z=z)).image flatPoint =
      maximalPoints (cornerSlice D z)\maximalPoints (cornerSlice D (z+1)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    obtain ⟨hp,hpz⟩ := mem_filter.mp hp
    obtain ⟨hmax,hnext⟩ := (maximal_slice_iff hd p).mp hp
    rw [hpz] at hmax hnext
    refine mem_sdiff.mpr ⟨hmax,?_⟩
    intro hm
    exact hnext ((mem_maximalPoints _ _).mp hm).1
  · intro hq
    obtain ⟨hq,hnot⟩ := mem_sdiff.mp hq
    have hflat := ((mem_maximalPoints _ _).mp hq).1
    have hqz := ((mem_cornerSlice _ _ _).mp hflat).1
    have hnext : q∉cornerSlice D (z+1) := by
      intro hnext
      exact hnot (maximal_mem_of_smaller_set (cornerSlice_antitone hd (by omega)) hq hnext)
    have he : flatPoint (liftPoint z q)=q := by ext <;> simp [flatPoint,liftPoint,hqz]
    refine mem_image.mpr ⟨liftPoint z q,mem_filter.mpr ⟨?_,rfl⟩,he⟩
    apply (maximal_slice_iff hd _).mpr
    change flatPoint (liftPoint z q)∈maximalPoints (cornerSlice D z) ∧
      flatPoint (liftPoint z q)∉cornerSlice D (z+1)
    rw [he]
    exact ⟨hq,hnext⟩

theorem cornerSlice_above_sup (D : Finset Point3) :
    cornerSlice D (D.sup Point3.z+1)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p
  intro hp
  have h := ((mem_cornerSlice _ _ _).mp hp).2
  have hz := le_sup (f := Point3.z) h
  change D.sup Point3.z+1≤D.sup Point3.z at hz
  omega

/-- Exact global decomposition, including the final empty layer. -/
theorem maximal_card_eq_layer_deaths {D : Finset Point3} (hd : IsDownset D) :
    (maximalPoints D).card = ∑ z∈range (D.sup Point3.z+1),
      (maximalPoints (cornerSlice D z)\maximalPoints (cornerSlice D (z+1))).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Point3.z) (t := range (D.sup Point3.z+1))
    (by
      intro p hp
      apply mem_range.mpr
      have hpD := ((mem_maximalPoints D p).mp hp).1
      have hz := le_sup (f := Point3.z) hpD
      omega)]
  apply sum_congr rfl
  intro z hz
  rw [← maximal_slice_image hd z,card_image_iff.mpr]
  intro p hp q hq he
  obtain ⟨_,hpz⟩ := mem_filter.mp hp
  obtain ⟨_,hqz⟩ := mem_filter.mp hq
  have hx := congrArg Point3.x he
  have hy := congrArg Point3.y he
  ext <;> simp_all [flatPoint]

/-- The remaining global obligation is only boundary-weight bookkeeping. -/
theorem maximal_card_le_oriented_layers {D : Finset Point3} (hd : IsDownset D) :
    (maximalPoints D).card ≤
      ((cornerBoundary (cornerSlice D 0)).filter (fun b => b.z=0 ∧ 0<b.x)).card +
      ∑ z∈range (D.sup Point3.z+1),
        (orientedCorners (cornerSlice D z) (cornerSlice D (z+1))).card := by
  classical
  have hbal := layer_birth_death_balance (fun z => maximalPoints (cornerSlice D z))
    (D.sup Point3.z+1)
  have hempty : maximalPoints (cornerSlice D (D.sup Point3.z+1))=∅ := by
    rw [cornerSlice_above_sup]
    ext p
    simp [mem_maximalPoints]
  rw [hempty,card_empty,Nat.add_zero,← maximal_card_eq_layer_deaths hd] at hbal
  rw [hbal]
  apply Nat.add_le_add
  · exact planar_maxima_le_x_corners _ (cornerSlice_downset hd 0) (cornerSlice_planar D 0)
  · apply sum_le_sum
    intro z hz
    exact planar_births_le_oriented _ _ (cornerSlice_downset hd z)
      (cornerSlice_downset hd (z+1)) (cornerSlice_planar D z)
      (cornerSlice_antitone hd (by omega))

end NSP3.V03
