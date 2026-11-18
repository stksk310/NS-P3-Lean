import NSP3.V03.BettiApery
import NSP3.BoundaryDescent

/-!
Planar layer births inject into oriented minimal-complement corners.
The boundary definition includes the origin, so the empty planar layer has
boundary {0}; its origin has no positive orientation and pays zero units.
-/
namespace NSP3.V03
open Finset

set_option maxHeartbeats 2000000

/-- A boundary finset for any finite set, including the empty set. -/
noncomputable def cornerBoundary (D : Finset Point3) : Finset Point3 := by
  classical
  exact ({Point3.zero} ∪ (D.image fun p => p+Point3.e1) ∪
    (D.image fun p => p+Point3.e2) ∪ (D.image fun p => p+Point3.e3)).filter
      (MinimalComplement D)

@[simp] theorem mem_cornerBoundary (D : Finset Point3) (b : Point3) :
    b∈cornerBoundary D ↔ MinimalComplement D b := by
  classical
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro hb
    apply mem_filter.mpr
    refine ⟨?_,hb⟩
    by_cases hx : 0<b.x
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _
        (mem_image.mpr ⟨b.pred1,hb.pred1_mem hx,b.pred1_add_e1 hx⟩)))
    by_cases hy : 0<b.y
    · exact mem_union_left _ (mem_union_right _
        (mem_image.mpr ⟨b.pred2,hb.pred2_mem hy,b.pred2_add_e2 hy⟩))
    by_cases hz : 0<b.z
    · exact mem_union_right _ (mem_image.mpr
        ⟨b.pred3,hb.pred3_mem hz,b.pred3_add_e3 hz⟩)
    have heq : b=Point3.zero := by
      apply Point3.ext <;> simp only [Point3.zero_x,Point3.zero_y,Point3.zero_z] <;> omega
    exact mem_union_left _ (mem_union_left _ (mem_union_left _ (by simp [heq])))

@[simp] theorem cornerBoundary_empty : cornerBoundary ∅={Point3.zero} := by
  classical
  ext p
  rw [mem_cornerBoundary]
  constructor
  · intro hp
    have hx : p.x=0 := by
      by_contra h; have := hp.pred1_mem (by omega); simp at this
    have hy : p.y=0 := by
      by_contra h; have := hp.pred2_mem (by omega); simp at this
    have hz : p.z=0 := by
      by_contra h; have := hp.pred3_mem (by omega); simp at this
    have heq : p=Point3.zero := by ext <;> simp_all
    simp [heq]
  · intro hp
    have heq : p=Point3.zero := by simpa using hp
    subst p
    simp [MinimalComplement,Point3.zero,Point3.pred1,Point3.pred2,Point3.pred3]

/-- A planar slice is represented at z=0, using the existing maximalPoints API. -/
def Planar (D : Finset Point3) : Prop := ∀ p∈D,p.z=0

theorem planar_maximal_x_injective {D : Finset Point3} (hpl : Planar D)
    {p q : Point3} (hp : p∈maximalPoints D) (hq : q∈maximalPoints D)
    (hx : p.x=q.x) : p=q := by
  have hp' := (mem_maximalPoints D p).mp hp
  have hq' := (mem_maximalPoints D q).mp hq
  have hpz := hpl p hp'.1
  have hqz := hpl q hq'.1
  rcases le_total p.y q.y with hy | hy
  · exact (hp'.2 q hq'.1 ⟨by omega,hy,by omega⟩).symm
  · exact hq'.2 p hp'.1 ⟨by omega,hy,by omega⟩

theorem planar_maximal_y_injective {D : Finset Point3} (hpl : Planar D)
    {p q : Point3} (hp : p∈maximalPoints D) (hq : q∈maximalPoints D)
    (hy : p.y=q.y) : p=q := by
  have hp' := (mem_maximalPoints D p).mp hp
  have hq' := (mem_maximalPoints D q).mp hq
  have hpz := hpl p hp'.1
  have hqz := hpl q hq'.1
  rcases le_total p.x q.x with hx | hx
  · exact (hp'.2 q hq'.1 ⟨hx,by omega,by omega⟩).symm
  · exact hq'.2 p hp'.1 ⟨hx,by omega,by omega⟩

theorem maximal_succ1_not_mem {D : Finset Point3} {p : Point3}
    (hp : p∈maximalPoints D) : p+Point3.e1∉D := by
  intro hs
  have hm := (mem_maximalPoints D p).mp hp
  have heq := hm.2 (p+Point3.e1) hs (by
    change p.x≤p.x+1 ∧ p.y≤p.y+0 ∧ p.z≤p.z+0
    omega)
  have hx := congrArg Point3.x heq
  simp only [Point3.add_x,Point3.e1_x] at hx
  omega

theorem maximal_succ2_not_mem {D : Finset Point3} {p : Point3}
    (hp : p∈maximalPoints D) : p+Point3.e2∉D := by
  intro hs
  have hm := (mem_maximalPoints D p).mp hp
  have heq := hm.2 (p+Point3.e2) hs (by
    change p.x≤p.x+0 ∧ p.y≤p.y+1 ∧ p.z≤p.z+0
    omega)
  have hy := congrArg Point3.y heq
  simp only [Point3.add_y,Point3.e2_y] at hy
  omega

theorem corner_below_succ1_preserves_x {D : Finset Point3} (hD : IsDownset D)
    {p b : Point3} (hp : p∈D) (hb : MinimalComplement D b)
    (hle : b≤p+Point3.e1) : b.x=p.x+1 := by
  have hx : b.x≤p.x+1 := by simpa using hle.1
  by_contra heq
  have hb' : b≤p := ⟨by omega,by simpa using hle.2.1,by simpa using hle.2.2⟩
  exact hb.not_mem (hD hb' hp)

theorem corner_below_succ2_preserves_y {D : Finset Point3} (hD : IsDownset D)
    {p b : Point3} (hp : p∈D) (hb : MinimalComplement D b)
    (hle : b≤p+Point3.e2) : b.y=p.y+1 := by
  have hy : b.y≤p.y+1 := by simpa using hle.2.1
  by_contra heq
  have hb' : b≤p := ⟨by simpa using hle.1,by omega,by simpa using hle.2.2⟩
  exact hb.not_mem (hD hb' hp)

theorem planar_maximal_extension {E F : Finset Point3}
    (hE : IsDownset E) (hpl : Planar E) (hFE : F⊆E)
    {p : Point3} (hp : p∈maximalPoints F) (hn : p∉maximalPoints E) :
    p+Point3.e1∈E ∨ p+Point3.e2∈E := by
  have hpF := ((mem_maximalPoints F p).mp hp).1
  have hpE := hFE hpF
  have hpz := hpl p hpE
  by_contra hext
  push Not at hext
  apply hn
  apply (mem_maximalPoints E p).mpr
  refine ⟨hpE,?_⟩
  intro q hq hpq
  have hqz := hpl q hq
  have hx : q.x=p.x := by
    by_contra h
    have hlt : p.x+1≤q.x := by have := hpq.1; omega
    apply hext.1
    apply hE (b := q) ?_ hq
    change p.x+1≤q.x ∧ p.y+0≤q.y ∧ p.z+0≤q.z
    exact ⟨hlt,hpq.2.1,hpq.2.2⟩
  have hy : q.y=p.y := by
    by_contra h
    have hlt : p.y+1≤q.y := by have := hpq.2.1; omega
    apply hext.2
    apply hE (b := q) ?_ hq
    change p.x+0≤q.x ∧ p.y+1≤q.y ∧ p.z+0≤q.z
    exact ⟨hpq.1,hlt,hpq.2.2⟩
  apply Point3.ext <;> omega

/-- false is the x-orientation; true is the y-orientation. -/
noncomputable def orientedCorners (E F : Finset Point3) : Finset (Point3×Bool) := by
  classical
  exact ((cornerBoundary F∩E).product univ).filter
    (fun v => if v.2 then 0<v.1.y else 0<v.1.x)

@[simp] theorem mem_orientedCorners (E F : Finset Point3) (b : Point3) (i : Bool) :
    (b,i)∈orientedCorners E F ↔
      MinimalComplement F b ∧ b∈E ∧ (if i then 0<b.y else 0<b.x) := by
  classical
  simp [orientedCorners,and_assoc]

/-- New maximal points inject into real oriented corners; no path certificate. -/
theorem planar_births_le_oriented (E F : Finset Point3)
    (hE : IsDownset E) (hF : IsDownset F) (hpl : Planar E) (hFE : F⊆E) :
    (maximalPoints F\maximalPoints E).card≤(orientedCorners E F).card := by
  classical
  let A := {p : Point3 // p∈maximalPoints F\maximalPoints E}
  let B := {v : Point3×Bool // v∈orientedCorners E F}
  have hplF : Planar F := fun p hp => hpl p (hFE hp)
  have hex (p : A) : ∃ v : B,
      if v.val.2 then v.val.1.y=p.val.y+1 else v.val.1.x=p.val.x+1 := by
    have hp := mem_sdiff.mp p.property
    rcases planar_maximal_extension hE hpl hFE hp.1 hp.2 with hx | hy
    · obtain ⟨b,hb,hle⟩ := exists_minimalComplement_le (maximal_succ1_not_mem hp.1)
      have heq := corner_below_succ1_preserves_x hF
        ((mem_maximalPoints F p.val).mp hp.1).1 hb hle
      have hbE := hE hle hx
      let v : B := ⟨(b,false),(mem_orientedCorners E F b false).mpr
        ⟨hb,hbE,by simp; omega⟩⟩
      exact ⟨v,heq⟩
    · obtain ⟨b,hb,hle⟩ := exists_minimalComplement_le (maximal_succ2_not_mem hp.1)
      have heq := corner_below_succ2_preserves_y hF
        ((mem_maximalPoints F p.val).mp hp.1).1 hb hle
      have hbE := hE hle hy
      let v : B := ⟨(b,true),(mem_orientedCorners E F b true).mpr
        ⟨hb,hbE,by simp; omega⟩⟩
      exact ⟨v,heq⟩
  let f : A→B := fun p => Classical.choose (hex p)
  have hspec (p : A) :
      if (f p).val.2 then (f p).val.1.y=p.val.y+1 else
        (f p).val.1.x=p.val.x+1 := Classical.choose_spec (hex p)
  have hinj : Function.Injective f := by
    intro p q heq
    have hp := hspec p
    have hq := hspec q
    rw [heq] at hp
    apply Subtype.ext
    have hpM := (mem_sdiff.mp p.property).1
    have hqM := (mem_sdiff.mp q.property).1
    cases hflag : (f q).val.2 with
    | false =>
        simp [hflag] at hp hq
        exact planar_maximal_x_injective hplF hpM hqM (by omega)
    | true =>
        simp [hflag] at hp hq
        exact planar_maximal_y_injective hplF hpM hqM (by omega)
  simpa [A,B] using Fintype.card_le_of_injective f hinj

/-- The base layer uses only the positive-x, z=0 corners. -/
theorem planar_maxima_le_x_corners (E : Finset Point3)
    (hE : IsDownset E) (hpl : Planar E) :
    (maximalPoints E).card≤((cornerBoundary E).filter
      (fun b => b.z=0 ∧ 0<b.x)).card := by
  classical
  let A := {p : Point3 // p∈maximalPoints E}
  let B := {b : Point3 // b∈(cornerBoundary E).filter (fun b => b.z=0 ∧ 0<b.x)}
  letI : Fintype A := by dsimp [A]; infer_instance
  letI : Fintype B := by dsimp [B]; infer_instance
  have hex (p : A) : ∃ b : B,b.val.x=p.val.x+1 := by
    obtain ⟨b,hb,hle⟩ := exists_minimalComplement_le (maximal_succ1_not_mem p.property)
    have hpE := ((mem_maximalPoints E p.val).mp p.property).1
    have hx := corner_below_succ1_preserves_x hE hpE hb hle
    have hpz := hpl p.val hpE
    have hbz : b.z=0 := by have := hle.2.2; simp only [Point3.add_z,Point3.e1_z] at this; omega
    exact ⟨⟨b,mem_filter.mpr ⟨(mem_cornerBoundary E b).mpr hb,⟨hbz,by omega⟩⟩⟩,hx⟩
  let f : A→B := fun p => Classical.choose (hex p)
  have hinj : Function.Injective f := by
    intro p q heq
    apply Subtype.ext
    have hp := Classical.choose_spec (hex p)
    have hq := Classical.choose_spec (hex q)
    change (f p).val.x=p.val.x+1 at hp
    change (f q).val.x=q.val.x+1 at hq
    rw [heq] at hp
    exact planar_maximal_x_injective hpl p.property q.property (by omega)
  simpa [A,B] using Fintype.card_le_of_injective f hinj

end NSP3.V03
