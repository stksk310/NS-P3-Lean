import NSP3.PlaneResources

namespace NSP3

noncomputable section

example (S : CyclicStaircase) (p : Point3) :
    p ∈ plane12PosFinset S ↔ p ∈ S.D ∧ 0 < p.x ∧ 0 < p.y ∧ p.z = 0 :=
  mem_plane12PosFinset S p

example (S : CyclicStaircase) :
    (plane12PosFinset S).card =
      Nat.choose (pair12Count S.D) 2 + (pair12ExtraFinset S).card :=
  card_plane12PosFinset S

example (S : CyclicStaircase)
    (h : (pair13ExtraFinset S).card = 0) : Pair13PlaneExact S :=
  pair13PlaneExact_of_extra_card_eq_zero S h

example (S : CyclicStaircase) (h : ¬ Pair23PlaneExact S) :
    1 ≤ (pair23ExtraFinset S).card :=
  pair23Extra_card_pos_of_not_exact S h

end

end NSP3
