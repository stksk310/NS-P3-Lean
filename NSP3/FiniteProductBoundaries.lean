import NSP3.FiniteSeedFilters

namespace NSP3

/-- Nested product-volume bounds avoid materializing an (m+1)³ cube. -/
def productBoundaries (m : ℕ) : Finset Point3 :=
  (((Finset.range (m+1)).biUnion fun x =>
    (Finset.range ((m+1)/(x+1))).biUnion fun y =>
      (Finset.range ((m+1)/((x+1)*(y+1)))).image fun z =>
        (⟨x,y,z⟩ : Point3))).filter fun g =>
          FullSupport g ∧ (g.x+1)*(g.y+1)*(g.z+1)-1 ≤ m

theorem mem_productBoundaries (m : ℕ) (g : Point3) :
    g ∈ productBoundaries m ↔
      FullSupport g ∧ (g.x+1)*(g.y+1)*(g.z+1)-1 ≤ m := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hf,hp⟩
    have hxyz : (g.x+1)*(g.y+1)*(g.z+1) ≤ m+1 := by omega
    have hxy : (g.x+1)*(g.y+1) ≤ m+1 := by
      nlinarith [Nat.zero_le ((g.x+1)*(g.y+1)*g.z)]
    have hx : g.x+1 ≤ m+1 := by
      nlinarith [Nat.zero_le ((g.x+1)*g.y)]
    have hy : g.y+1 ≤ (m+1)/(g.x+1) := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      simpa only [Nat.mul_comm] using hxy
    have hz : g.z+1 ≤ (m+1)/((g.x+1)*(g.y+1)) := by
      apply (Nat.le_div_iff_mul_le (by positivity)).mpr
      simpa only [Nat.mul_comm] using hxyz
    apply Finset.mem_filter.mpr
    refine ⟨?_,hf,hp⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨g.x, Finset.mem_range.mpr (by omega), ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨g.y, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_image.mpr ⟨g.z,Finset.mem_range.mpr (by omega),by cases g; rfl⟩

theorem actual_boundary_mem_productBoundaries (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    g ∈ productBoundaries S.m :=
  (mem_productBoundaries S.m g).mpr ⟨hf,actual_boundary_product_bound S hg hf⟩

end NSP3
