import NSP3.SharpnessParameters
import NSP3.SharpnessApery

namespace NSP3.Sharpness

private def evenLeft (k : ℕ) : Finset Point3 :=
  (Finset.range (k+1)).image (fun j => ⟨j,k+1-j,0⟩)
private def evenRight (k : ℕ) : Finset Point3 :=
  (Finset.Icc 1 (k+1)).image (fun j => ⟨0,k+1-j,j⟩)
private def oddLeft (k : ℕ) : Finset Point3 :=
  (Finset.Icc 1 k).image (fun j => ⟨j,k+1-j,0⟩)
private def oddRight (k : ℕ) : Finset Point3 :=
  (Finset.Icc 1 k).image (fun j => ⟨0,k-j,j⟩)

/-- The even construction's two corner points and two sloping boundary chains. -/
def evenBorder (L k : ℕ) : Finset Point3 :=
  insert ⟨1,0,1⟩ (insert ⟨L,0,0⟩ (evenLeft k ∪ evenRight k))

/-- The odd construction has a third pure corner and shorter boundary chains. -/
def oddBorder (L k : ℕ) : Finset Point3 :=
  insert ⟨1,0,1⟩ (insert ⟨L+1,0,0⟩ (insert ⟨0,k+1,0⟩ (oddLeft k ∪ oddRight k)))

/-- Literal indexed membership, suitable for computing each border weight. -/
theorem evenBorder_mem (L k : ℕ) (p : Point3) :
    p ∈ evenBorder L k ↔
      p = ⟨1,0,1⟩ ∨ p = ⟨L,0,0⟩ ∨
      (∃ j, j ≤ k ∧ p = ⟨j,k+1-j,0⟩) ∨
      (∃ j, 1 ≤ j ∧ j ≤ k+1 ∧ p = ⟨0,k+1-j,j⟩) := by
  simp [evenBorder,evenLeft,evenRight,eq_comm,and_assoc]

/-- Literal indexed membership for the odd construction. -/
theorem oddBorder_mem (L k : ℕ) (p : Point3) :
    p ∈ oddBorder L k ↔
      p = ⟨1,0,1⟩ ∨ p = ⟨L+1,0,0⟩ ∨ p = ⟨0,k+1,0⟩ ∨
      (∃ j, 1 ≤ j ∧ j ≤ k ∧ p = ⟨j,k+1-j,0⟩) ∨
      (∃ j, 1 ≤ j ∧ j ≤ k ∧ p = ⟨0,k-j,j⟩) := by
  simp [oddBorder,oddLeft,oddRight,eq_comm,and_assoc]

private theorem mem_evenLeft (k : ℕ) (p : Point3) :
    p ∈ evenLeft k ↔ p.z=0 ∧ 0 < p.y ∧ p.x+p.y=k+1 := by
  simp only [evenLeft,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩
    dsimp
    omega
  · rintro ⟨hz,hy,hxy⟩
    refine ⟨p.x,by omega,?_⟩
    apply Point3.ext <;> dsimp <;> omega

private theorem mem_evenRight (k : ℕ) (p : Point3) :
    p ∈ evenRight k ↔ p.x=0 ∧ 0 < p.z ∧ p.y+p.z=k+1 := by
  simp only [evenRight,Finset.mem_image,Finset.mem_Icc]
  constructor
  · rintro ⟨j,⟨hj,hj'⟩,rfl⟩
    dsimp
    omega
  · rintro ⟨hx,hz,hyz⟩
    refine ⟨p.z,⟨by omega,by omega⟩,?_⟩
    apply Point3.ext <;> dsimp <;> omega

private theorem mem_oddLeft (k : ℕ) (p : Point3) :
    p ∈ oddLeft k ↔ p.z=0 ∧ 0 < p.x ∧ 0 < p.y ∧ p.x+p.y=k+1 := by
  simp only [oddLeft,Finset.mem_image,Finset.mem_Icc]
  constructor
  · rintro ⟨j,⟨hj,hj'⟩,rfl⟩
    dsimp
    omega
  · rintro ⟨hz,hx,hy,hxy⟩
    refine ⟨p.x,⟨by omega,by omega⟩,?_⟩
    apply Point3.ext <;> dsimp <;> omega

private theorem mem_oddRight (k : ℕ) (p : Point3) :
    p ∈ oddRight k ↔ p.x=0 ∧ 0 < p.z ∧ p.y+p.z=k := by
  simp only [oddRight,Finset.mem_image,Finset.mem_Icc]
  constructor
  · rintro ⟨j,⟨hj,hj'⟩,rfl⟩
    dsimp
    omega
  · rintro ⟨hx,hz,hyz⟩
    refine ⟨p.z,⟨by omega,by omega⟩,?_⟩
    apply Point3.ext <;> dsimp <;> omega

private theorem evenLeft_card (k : ℕ) : (evenLeft k).card = k+1 := by
  unfold evenLeft
  rw [Finset.card_image_iff.mpr ?_,Finset.card_range]
  intro i _ j _ h
  exact congrArg Point3.x h

private theorem evenRight_card (k : ℕ) : (evenRight k).card = k+1 := by
  unfold evenRight
  rw [Finset.card_image_iff.mpr ?_]
  · simp
  · intro i _ j _ h
    exact congrArg Point3.z h

private theorem oddLeft_card (k : ℕ) : (oddLeft k).card = k := by
  unfold oddLeft
  rw [Finset.card_image_iff.mpr ?_]
  · simp
  · intro i _ j _ h
    exact congrArg Point3.x h

private theorem oddRight_card (k : ℕ) : (oddRight k).card = k := by
  unfold oddRight
  rw [Finset.card_image_iff.mpr ?_]
  · simp
  · intro i _ j _ h
    exact congrArg Point3.z h

/-- Exact even boundary count, with every inserted point and chain disjoint. -/
theorem evenBorder_card (L k : ℕ) (_hk : 1 ≤ k) (_hL : k < L) :
    (evenBorder L k).card = 2*k+4 := by
  have hd : Disjoint (evenLeft k) (evenRight k) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rw [mem_evenLeft] at hp
    rw [mem_evenRight] at hq
    omega
  have hp : (⟨L,0,0⟩ : Point3) ∉ evenLeft k ∪ evenRight k := by
    simp [mem_evenLeft,mem_evenRight]
  have hac : (⟨1,0,1⟩ : Point3) ∉ insert ⟨L,0,0⟩ (evenLeft k ∪ evenRight k) := by
    simp [mem_evenLeft,mem_evenRight,Point3.mk.injEq]
  unfold evenBorder
  rw [Finset.card_insert_of_notMem hac,Finset.card_insert_of_notMem hp,
    Finset.card_union_of_disjoint hd,evenLeft_card,evenRight_card]
  omega

/-- Exact odd boundary count, including the separate pure-y corner. -/
theorem oddBorder_card (L k : ℕ) (_hk : 2 ≤ k) (_hL : k ≤ L) :
    (oddBorder L k).card = 2*k+3 := by
  have hd : Disjoint (oddLeft k) (oddRight k) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rw [mem_oddLeft] at hp
    rw [mem_oddRight] at hq
    omega
  have hy : (⟨0,k+1,0⟩ : Point3) ∉ oddLeft k ∪ oddRight k := by
    simp [mem_oddLeft,mem_oddRight]
  have hp : (⟨L+1,0,0⟩ : Point3) ∉ insert ⟨0,k+1,0⟩ (oddLeft k ∪ oddRight k) := by
    simp [mem_oddLeft,mem_oddRight,Point3.mk.injEq]
  have hac : (⟨1,0,1⟩ : Point3) ∉
      insert ⟨L+1,0,0⟩ (insert ⟨0,k+1,0⟩ (oddLeft k ∪ oddRight k)) := by
    simp [mem_oddLeft,mem_oddRight,Point3.mk.injEq]
  unfold oddBorder
  rw [Finset.card_insert_of_notMem hac,Finset.card_insert_of_notMem hp,
    Finset.card_insert_of_notMem hy,Finset.card_union_of_disjoint hd,
    oddLeft_card,oddRight_card]
  omega




/-- Every immediate predecessor in a positive coordinate returns to the even region. -/
theorem evenBorder_predecessors (L k : ℕ) (hk : 1 ≤ k) (_hL : k < L)
    {p : Point3} (hp : p ∈ evenBorder L k) :
    (0 < p.x → EvenRegion L k (Point3.pred1 p)) ∧
    (0 < p.y → EvenRegion L k (Point3.pred2 p)) ∧
    (0 < p.z → EvenRegion L k (Point3.pred3 p)) := by
  rcases (evenBorder_mem L k p).mp hp with rfl | rfl | ⟨j,hj,rfl⟩ | ⟨j,hj,hj',rfl⟩ <;>
    simp_all [EvenRegion,Point3.pred1,Point3.pred2,Point3.pred3] <;> omega

/-- Every immediate predecessor in a positive coordinate returns to the odd region. -/
theorem oddBorder_predecessors (L k : ℕ) (hk : 2 ≤ k) (_hL : k ≤ L)
    {p : Point3} (hp : p ∈ oddBorder L k) :
    (0 < p.x → OddRegion L k (Point3.pred1 p)) ∧
    (0 < p.y → OddRegion L k (Point3.pred2 p)) ∧
    (0 < p.z → OddRegion L k (Point3.pred3 p)) := by
  rcases (oddBorder_mem L k p).mp hp with rfl | rfl | rfl |
      ⟨j,hj,hj',rfl⟩ | ⟨j,hj,hj',rfl⟩ <;>
    simp_all [OddRegion,Point3.pred1,Point3.pred2,Point3.pred3] <;> omega

end NSP3.Sharpness

