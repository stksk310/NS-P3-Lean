import NSP3.MandatorySeed

namespace NSP3

private instance pointLEDecidable (a b : Point3) : Decidable (a ≤ b) := by
  change Decidable (a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.z ≤ b.z)
  infer_instance

/-- Inclusive rectangular box, with no sum-sized ambient cube. -/
def seedRect (x y z : ℕ) : Finset Point3 :=
  ((Finset.range (x+1)).product
    ((Finset.range (y+1)).product (Finset.range (z+1)))).image
      fun a => Point3.mk a.1 a.2.1 a.2.2

@[simp] theorem mem_seedRect (x y z : ℕ) (p : Point3) :
    p ∈ seedRect x y z ↔ p.x ≤ x ∧ p.y ≤ y ∧ p.z ≤ z := by
  constructor
  · intro hp
    obtain ⟨⟨a,b,c⟩,h,he⟩ := Finset.mem_image.mp hp
    subst p
    simpa [Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff] using h
  · intro h
    refine Finset.mem_image.mpr ⟨(p.x,p.y,p.z),?_,?_⟩
    · simpa [Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff] using h
    · ext <;> rfl

/-- Seven tight pieces: punctured box, forced axes, three Ferrers planes,
and punctured positive core. For ordered q its downward closure is proved;
arbitrary unordered q use the exact closure below. -/
def fastRawMandatorySeed (q : FullResidualTuple) (g : Point3) : Finset Point3 :=
  ((seedRect g.x g.y g.z).filter fun p => p ≠ g) ∪
  (seedRect q.r 0 0 ∪ seedRect 0 q.r 0 ∪ seedRect 0 0 q.s) ∪
  ((seedRect q.r q.r 0).filter fun p =>
    0 < p.x ∧ 0 < p.y ∧ p.x+p.y ≤ q.r) ∪
  ((seedRect q.s 0 q.s).filter fun p =>
    0 < p.x ∧ 0 < p.z ∧ p.x+p.z ≤ q.s) ∪
  ((seedRect 0 q.t q.t).filter fun p =>
    0 < p.y ∧ 0 < p.z ∧ p.y+p.z ≤ q.t) ∪
  ((seedRect q.r q.r q.s).filter fun p =>
    0 < p.x ∧ 0 < p.y ∧ 0 < p.z ∧
    p.x+p.y ≤ q.r ∧ p.x+p.z ≤ q.s ∧ p.y+p.z ≤ q.t ∧ ¬ g ≤ p)

@[simp] theorem mem_fastRawMandatorySeed (q : FullResidualTuple) (g p : Point3) :
    p ∈ fastRawMandatorySeed q g ↔ MandatorySeedPred q g p := by
  simp only [fastRawMandatorySeed,Finset.mem_union,Finset.mem_filter,mem_seedRect,
    Nat.le_zero,or_assoc,and_assoc]
  unfold MandatorySeedPred
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl ⟨⟨h.1,h.2.1,h.2.2.1⟩,h.2.2.2⟩
    all_goals try omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.2.2.2))))))
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl ⟨h.1.1,h.1.2.1,h.1.2.2,h.2⟩
    all_goals try omega
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
    exact ⟨by omega,by omega,by omega,h⟩

def fastSeedLowerBox (p : Point3) : Finset Point3 := seedRect p.x p.y p.z

theorem fastSeedLowerBox_eq (p : Point3) : fastSeedLowerBox p = seedLowerBox p := by
  ext a
  simp only [fastSeedLowerBox,mem_seedRect,mem_seedLowerBox]
  rfl

theorem mandatorySeedPred_downward_ordered {q : FullResidualTuple} {g a b : Point3}
    (hs : q.s ≤ q.r) (ht : q.t ≤ q.s) (hab : a ≤ b)
    (hb : MandatorySeedPred q g b) : MandatorySeedPred q g a := by
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb
  · exact Or.inl ⟨le_trans hab hb.1,fun he =>
      hb.2 (le_antisymm hb.1 (he ▸ hab))⟩
  all_goals try
    unfold MandatorySeedPred
    change a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.z ≤ b.z at hab
    omega
  have hng : ¬ g ≤ a := fun hga => hb.2.2.2.2.2.2 (le_trans hga hab)
  by_cases hx : a.x = 0
  · unfold MandatorySeedPred
    change a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.z ≤ b.z at hab
    omega
  by_cases hy : a.y = 0
  · unfold MandatorySeedPred
    change a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.z ≤ b.z at hab
    omega
  by_cases hz : a.z = 0
  · unfold MandatorySeedPred
    change a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.z ≤ b.z at hab
    omega
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
  change a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.z ≤ b.z at hab
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,hng⟩

/-- Exact downward closure also for unordered q. -/
def fastMandatorySeed (q : FullResidualTuple) (g : Point3) : Finset Point3 :=
  if q.s ≤ q.r ∧ q.t ≤ q.s then fastRawMandatorySeed q g
  else (fastRawMandatorySeed q g).biUnion fastSeedLowerBox

theorem fastMandatorySeed_ordered_eq (q : FullResidualTuple) (g : Point3)
    (hs : q.s ≤ q.r) (ht : q.t ≤ q.s) :
    fastMandatorySeed q g = fastRawMandatorySeed q g := by
  simp [fastMandatorySeed,hs,ht]

theorem fastMandatorySeed_eq (q : FullResidualTuple) (g : Point3) :
    fastMandatorySeed q g = mandatorySeed q g := by
  ext p
  unfold fastMandatorySeed
  split
  · rename_i h
    rw [mem_fastRawMandatorySeed,mem_mandatorySeed]
    constructor
    · intro hp
      exact ⟨p,(mem_rawMandatorySeed q g p).mpr hp,le_rfl⟩
    · rintro ⟨b,hb,hpb⟩
      exact mandatorySeedPred_downward_ordered h.1 h.2 hpb
        ((mem_rawMandatorySeed q g b).mp hb)
  · simp only [Finset.mem_biUnion,fastSeedLowerBox_eq,
      mem_seedLowerBox,mem_fastRawMandatorySeed,mem_mandatorySeed,mem_rawMandatorySeed]

end NSP3
