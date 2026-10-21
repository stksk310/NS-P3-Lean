import NSP3.FullBoundaryAPI

namespace NSP3

noncomputable def lowerBoxFinset (g : Point3) : Finset Point3 := by
  classical
  exact (((Finset.range (g.x + 1)).product
    ((Finset.range (g.y + 1)).product (Finset.range (g.z + 1)))).image
      (fun a => Point3.mk a.1 a.2.1 a.2.2)).erase g

@[simp] theorem mem_lowerBoxFinset (g p : Point3) :
    p ∈ lowerBoxFinset g ↔ p ≤ g ∧ p ≠ g := by
  classical
  constructor
  · intro hp
    rcases Finset.mem_erase.mp hp with ⟨hne, himage⟩
    rcases Finset.mem_image.mp himage with ⟨a, ha, heq⟩
    rcases Finset.mem_product.mp ha with ⟨hx, ha23⟩
    rcases Finset.mem_product.mp ha23 with ⟨hy, hz⟩
    simp only [Finset.mem_range] at hx hy hz
    change Point3.mk a.1 a.2.1 a.2.2 = p at heq
    subst p
    exact ⟨⟨Nat.le_of_lt_succ hx, Nat.le_of_lt_succ hy,
      Nat.le_of_lt_succ hz⟩, hne⟩
  · rintro ⟨⟨hx, hy, hz⟩, hne⟩
    apply Finset.mem_erase.mpr
    refine ⟨hne, Finset.mem_image.mpr ⟨(p.x, (p.y, p.z)), ?_, rfl⟩⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hx), ?_⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hy),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hz)⟩

theorem lowerBoxFinset_subset_D {S : CyclicStaircase} {g : Point3}
    (hg : MinimalComplement S.D g) : lowerBoxFinset g ⊆ S.D := by
  intro p hp
  have h := (mem_lowerBoxFinset g p).mp hp
  rcases h.1 with ⟨hx, hy, hz⟩
  by_cases hxe : p.x = g.x
  · by_cases hye : p.y = g.y
    · have hzl : p.z < g.z := by
        have : p.z ≠ g.z := by intro hze; apply h.2; ext <;> assumption
        omega
      have hle : p ≤ g.pred3 := by
        change p.x ≤ g.x ∧ p.y ≤ g.y ∧ p.z ≤ g.z - 1
        omega
      exact S.down_closed.mem_of_le hle
        (hg.pred3_mem (by omega))
    · have hyl : p.y < g.y := by omega
      have hle : p ≤ g.pred2 := by
        change p.x ≤ g.x ∧ p.y ≤ g.y - 1 ∧ p.z ≤ g.z
        omega
      exact S.down_closed.mem_of_le hle
        (hg.pred2_mem (by omega))
  · have hxl : p.x < g.x := by omega
    have hle : p ≤ g.pred1 := by
      change p.x ≤ g.x - 1 ∧ p.y ≤ g.y ∧ p.z ≤ g.z
      omega
    exact S.down_closed.mem_of_le hle
      (hg.pred1_mem (by omega))

@[simp] theorem card_lowerBoxFinset (g : Point3) :
    (lowerBoxFinset g).card = (g.x + 1) * (g.y + 1) * (g.z + 1) - 1 := by
  classical
  let triples := (Finset.range (g.x + 1)).product
    ((Finset.range (g.y + 1)).product (Finset.range (g.z + 1)))
  let f : ℕ × (ℕ × ℕ) → Point3 := fun a => Point3.mk a.1 a.2.1 a.2.2
  have hinj : Set.InjOn f triples := by
    intro a ha b hb hab
    rcases a with ⟨ax, ⟨ay, az⟩⟩
    rcases b with ⟨bx, ⟨byc, bz⟩⟩
    simp only [f] at hab
    simp only [Prod.mk.injEq]
    exact ⟨congrArg Point3.x hab,
      ⟨congrArg Point3.y hab, congrArg Point3.z hab⟩⟩
  have hgmem : g ∈ triples.image f := by
    apply Finset.mem_image.mpr
    exact ⟨(g.x, (g.y, g.z)), by simp [triples], rfl⟩
  change ((triples.image f).erase g).card = _
  rw [Finset.card_erase_of_mem hgmem, Finset.card_image_of_injOn hinj]
  simp [triples, Nat.mul_assoc]

end NSP3
