import NSP3.FiniteNormalizedState

namespace NSP3

private def fastWeightsEmbedding (m : ℕ) :
    (ZMod m × (ZMod m × ZMod m)) ↪ ResidueWeights m where
  toFun a := ⟨a.1,a.2.1,a.2.2⟩
  inj' := by
    intro a b h
    rcases a with ⟨a1,a2,a3⟩
    rcases b with ⟨b1,b2,b3⟩
    simp only [Prod.mk.injEq]
    exact ⟨congrArg ResidueWeights.p1 h,
      congrArg ResidueWeights.p2 h,congrArg ResidueWeights.p3 h⟩

/-- Enumerate proper positive divisors before taking the two free coordinates.
The embedding is injective, so no quadratic image/union deduplication is needed.
Every p2/p3 is retained, including all nonunit lifts. -/
def fastDivisorResidueWeights (m : ℕ) [NeZero m] : Finset (ResidueWeights m) :=
  (((Finset.univ : Finset (ZMod m)).filter fun a => 0 < a.val ∧ a.val ∣ m).product
    ((Finset.univ : Finset (ZMod m)).product (Finset.univ : Finset (ZMod m)))).map
      (fastWeightsEmbedding m)

theorem fastDivisorResidueWeights_eq (m : ℕ) [NeZero m] :
    fastDivisorResidueWeights m = divisorResidueWeights m := by
  ext w
  constructor
  · intro hw
    obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hw
    have hd := (Finset.mem_filter.mp (Finset.mem_product.mp ha).1).2
    apply (mem_divisorResidueWeights w).mpr
    refine ⟨a.1.val,hd.1,ZMod.val_lt a.1,hd.2,?_⟩
    have hfirst : a.1 = w.p1 := congrArg ResidueWeights.p1 he
    exact hfirst.symm.trans (ZMod.natCast_zmod_val a.1).symm
  · intro hw
    obtain ⟨d,hpos,hlt,hdiv,he⟩ := (mem_divisorResidueWeights w).mp hw
    have hv : w.p1.val = d := by rw [he]; exact ZMod.val_natCast_of_lt hlt
    apply Finset.mem_map.mpr
    refine ⟨(w.p1,(w.p2,w.p3)),?_,?_⟩
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by simp⟩
      simpa only [hv] using And.intro hpos hdiv
    · cases w; rfl

end NSP3
