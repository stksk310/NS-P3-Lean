import NSP3.SymbolicTGE4Rows

namespace NSP3

-- Break caught: double-counting box/core overlap or failing to delete g.
example (S : CyclicStaircase) (g : Point3) (y z : ℕ) :
    ((fullSupportSymbolicH S g).filter (fun p => p.y=y ∧ p.z=z)).card =
      let L := if y+z ≤ pair23Count S.D then
        min (pair12Count S.D-y) (pair13Count S.D-z) else 0
      if y=0 ∨ z=0 then 0
      else if y ≤ g.y ∧ z ≤ g.z then
        if y=g.y ∧ z=g.z then g.x-1 else max g.x L
      else if g.y ≤ y ∧ g.z ≤ z then min (g.x-1) L else L :=
  symbolic_H_row_card S g y z

-- Break caught: the punctured core must not retain any point above the boundary.
example (S : CyclicStaircase) (g : Point3)
    (h : pair12Count S.D ≤ g.x ∨ pair12Count S.D ≤ g.y ∨ pair13Count S.D ≤ g.z) :
    fullCoreFinset S ⊆ fullSupportSymbolicH S g :=
  fullCore_subset_symbolic_H_of_large_coordinate S g h

end NSP3
