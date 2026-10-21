import NSP3.FiniteProductBoundaries
namespace NSP3

-- Inclusive punctured-box volume: g=(1,1,1) needs 7, not 8, points.
example : (⟨1,1,1⟩ : Point3) ∈ productBoundaries 7 := by decide
example : (⟨1,1,1⟩ : Point3) ∉ productBoundaries 6 := by decide
example : (⟨1,2,1⟩ : Point3) ∈ productBoundaries 11 := by decide
example : (⟨0,1,1⟩ : Point3) ∉ productBoundaries 7 := by decide

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    g ∈ productBoundaries S.m := actual_boundary_mem_productBoundaries S hg hf

end NSP3
