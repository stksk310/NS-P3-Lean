import NSP3.SharpnessApery
import NSP3.SharpnessBorders
namespace NSP3.Sharpness
example (L k : ℕ) (hk : 1 ≤ k) (hL : k < L) :
    (evenBorder L k).card = 2*k+4 := evenBorder_card L k hk hL
example (L k : ℕ) (hk : 2 ≤ k) (hL : k ≤ L) :
    (oddBorder L k).card = 2*k+3 := oddBorder_card L k hk hL
end NSP3.Sharpness

namespace NSP3.Sharpness

example (L k : ℕ) (p : Point3) :
    p ∈ evenBorder L k ↔ p = ⟨1,0,1⟩ ∨ p = ⟨L,0,0⟩ ∨
      (∃ j, j ≤ k ∧ p = ⟨j,k+1-j,0⟩) ∨
      (∃ j, 1 ≤ j ∧ j ≤ k+1 ∧ p = ⟨0,k+1-j,j⟩) :=
  evenBorder_mem L k p

example (L k : ℕ) (p : Point3) :
    p ∈ oddBorder L k ↔ p = ⟨1,0,1⟩ ∨ p = ⟨L+1,0,0⟩ ∨ p = ⟨0,k+1,0⟩ ∨
      (∃ j, 1 ≤ j ∧ j ≤ k ∧ p = ⟨j,k+1-j,0⟩) ∨
      (∃ j, 1 ≤ j ∧ j ≤ k ∧ p = ⟨0,k-j,j⟩) :=
  oddBorder_mem L k p

example : (evenBorder 2 1).card = 6 := evenBorder_card 2 1 (by omega) (by omega)
example : (oddBorder 2 2).card = 7 := oddBorder_card 2 2 (by omega) (by omega)

-- The shared y-axis endpoint belongs to only the left indexed even chain.
example : (⟨0,2,0⟩ : Point3) ∈ evenBorder 2 1 := by
  rw [evenBorder_mem]
  exact Or.inr (Or.inr (Or.inl ⟨0,by omega,rfl⟩))

-- The odd pure-y corner is separate from both indexed chains.
example : (⟨0,3,0⟩ : Point3) ∈ oddBorder 2 2 := by
  rw [oddBorder_mem]
  exact Or.inr (Or.inr (Or.inl rfl))

#print axioms evenBorder_mem
#print axioms oddBorder_mem
#print axioms evenBorder_card
#print axioms oddBorder_card

end NSP3.Sharpness


namespace NSP3.Sharpness
example (L k : ℕ) (hk : 1 ≤ k) (hL : k < L) {p : Point3}
    (hp : p ∈ evenBorder L k) :
    (0 < p.x → EvenRegion L k (Point3.pred1 p)) ∧
    (0 < p.y → EvenRegion L k (Point3.pred2 p)) ∧
    (0 < p.z → EvenRegion L k (Point3.pred3 p)) :=
  evenBorder_predecessors L k hk hL hp
example (L k : ℕ) (hk : 2 ≤ k) (hL : k ≤ L) {p : Point3}
    (hp : p ∈ oddBorder L k) :
    (0 < p.x → OddRegion L k (Point3.pred1 p)) ∧
    (0 < p.y → OddRegion L k (Point3.pred2 p)) ∧
    (0 < p.z → OddRegion L k (Point3.pred3 p)) :=
  oddBorder_predecessors L k hk hL hp
end NSP3.Sharpness

#print axioms NSP3.Sharpness.evenBorder_predecessors
#print axioms NSP3.Sharpness.oddBorder_predecessors
