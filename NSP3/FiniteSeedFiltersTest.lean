import NSP3.FiniteSeedFilters

namespace NSP3

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (mandatorySeed ⟨pair12Count S.D, pair13Count S.D, pair23Count S.D⟩ g).card ≤ S.m :=
  actual_mandatorySeed_card_le S hg hf

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    g ∉ mandatorySeed ⟨pair12Count S.D, pair13Count S.D, pair23Count S.D⟩ g :=
  actual_boundary_not_mem_mandatorySeed S hg hf

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (g.x+1)*(g.y+1)*(g.z+1)-1 ≤ S.m :=
  actual_boundary_product_bound S hg hf

end NSP3
