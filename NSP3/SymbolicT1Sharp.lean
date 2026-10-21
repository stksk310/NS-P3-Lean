import NSP3.SymbolicT3OrderedSharp
import NSP3.SmallTCofinal

namespace NSP3

theorem symbolic_H_positive_box_lower (S : CyclicStaircase) {g : Point3}
    (hfull : FullSupport g) :
    g.x * g.y * g.z - 1 ≤ (fullSupportSymbolicH S g).card := by
  classical
  have hxpos : 0 < g.x := hfull.1
  have hypos : 0 < g.y := hfull.2.1
  have hzpos : 0 < g.z := hfull.2.2
  have hxlt : g.x - 1 < g.x := by omega
  have hylt : g.y - 1 < g.y := by omega
  have hzlt : g.z - 1 < g.z := by omega
  let triples := (Finset.range g.x).product
    ((Finset.range g.y).product (Finset.range g.z))
  let point : ℕ × (ℕ × ℕ) → Point3 := fun a => Point3.mk (a.1 + 1) (a.2.1 + 1) (a.2.2 + 1)
  let points := triples.image point
  have hinj : Set.InjOn point triples := by
    intro a ha b hb hab
    apply Prod.ext
    · have hx := congrArg Point3.x hab
      simpa [point] using hx
    · apply Prod.ext
      · have hy := congrArg Point3.y hab
        simpa [point] using hy
      · have hz := congrArg Point3.z hab
        simpa [point] using hz
  have hgmem : g ∈ points := by
    apply Finset.mem_image.mpr
    refine ⟨(g.x - 1, (g.y - 1, g.z - 1)), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr hxlt, Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hylt, Finset.mem_range.mpr hzlt⟩⟩
    · apply Point3.ext <;> simp [point] <;> omega
  have hcard : (points.erase g).card = g.x * g.y * g.z - 1 := by
    rw [Finset.card_erase_of_mem hgmem]
    unfold points
    rw [Finset.card_image_iff.mpr hinj]
    simp [triples, Nat.mul_assoc]
  have hsub : points.erase g ⊆ fullSupportSymbolicH S g := by
    intro p hp
    have hdata := Finset.mem_erase.mp hp
    rcases Finset.mem_image.mp hdata.2 with ⟨a, ha, rfl⟩
    have ha' := Finset.mem_product.mp ha
    have hab := Finset.mem_product.mp ha'.2
    simp only [Finset.mem_range] at ha' hab
    apply Finset.mem_union.mpr; right
    apply Finset.mem_filter.mpr
    refine ⟨(mem_lowerBoxFinset _ _).mpr ⟨⟨by simp [point]; omega,
      by simp [point]; omega, by simp [point]; omega⟩, ?_⟩,
      ⟨by simp [point], by simp [point], by simp [point]⟩⟩
    exact fun heq => hdata.1 (heq ▸ rfl)
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- The positive box closes the small-r t1 region; the frozen cofinal theorem
    handles the infinite remainder. No finite checker or new certificate. -/
theorem fullSupport_t1_ordered_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=1) : fullTarget S ≤ S.m := by
  by_cases h4 : 4 ≤ pair12Count S.D
  · exact Nat.le_of_lt (fullSupport_t1_cofinal_strict S hg hf ho ht h4)
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hH := symbolic_H_positive_box_lower S hf
  have hx : 1 ≤ g.x := hf.1
  have hy : 1 ≤ g.y := hf.2.1
  have hz : 1 ≤ g.z := hf.2.2
  have ex : g.x-1+1=g.x := by omega
  have hxy : g.x+g.y ≤ g.x*g.y+1 := by
    have hm := Nat.mul_le_mul_left (g.x-1) hy
    have he := congrArg (fun n => n*g.y) ex
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_one] at he hm
    omega
  have hp : 1 ≤ g.x*g.y := le_trans hx (by simpa using Nat.mul_le_mul_left g.x hy)
  have ep : g.x*g.y-1+1=g.x*g.y := by omega
  have hxyz : g.x*g.y+g.z ≤ g.x*g.y*g.z+1 := by
    have hm := Nat.mul_le_mul_left (g.x*g.y-1) hz
    have he := congrArg (fun n => n*g.z) ep
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_one] at he hm
    omega
  have hH' : pair12Count S.D-1 ≤ (fullSupportSymbolicH S g).card := by omega
  have hb := fullSupport_symbolic_BW_lower S hg hf ho
  have ax := le_max_left (pair12Count S.D) g.x
  have ay := le_max_left (pair12Count S.D) g.y
  have az := le_max_left (pair12Count S.D) g.z
  have hd : ∀ n A B, 1 ≤ ferrersPlaneDefect n A B := by
    intro n A B
    exact le_max_left _ _
  have d12 := hd (pair12Count S.D) g.x g.y
  have d13 := hd (pair13Count S.D) g.x g.z
  have d23 := hd (pair23Count S.D) g.y g.z
  unfold fullSupportSymbolicBW at hb
  have hbudget : 1+3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+3+(pair12Count S.D-1) ≤ S.m := by
    rw [ht] at hb d23
    norm_num only [Nat.choose] at hb
    omega
  have hsr := ho.2
  have hs : 1 ≤ pair13Count S.D := by have := ho.1; omega
  have hr : 1 ≤ pair12Count S.D := by omega
  rw [fullTarget_eq_square,ht]
  interval_cases er : pair12Count S.D <;>
    interval_cases es : pair13Count S.D <;>
    norm_num [er,es,Nat.choose] at hbudget ⊢ <;> omega

end NSP3

