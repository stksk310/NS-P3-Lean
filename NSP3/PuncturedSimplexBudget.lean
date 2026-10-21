import NSP3.FullAccounting
import NSP3.CoreHoleCap

namespace NSP3

private noncomputable def orderedSimplexFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact Finset.univ.image
    (orderedSimplexPoint (pair13Count S.D) (pair23Count S.D))

noncomputable def orderedSimplexPunctured (S : CyclicStaircase) (g : Point3) :
    Finset Point3 := by
  classical
  exact (orderedSimplexFinset S).filter fun p => ¬ g ≤ p

private theorem card_orderedSimplexFinset (S : CyclicStaircase) :
    (orderedSimplexFinset S).card = simplexCard (pair13Count S.D) (pair23Count S.D) := by
  classical
  rw [orderedSimplexFinset, Finset.card_image_iff.mpr]
  · simp
  · exact fun _ _ _ _ h => orderedSimplexPoint_injective _ _ h

private theorem mem_orderedSimplexFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ orderedSimplexFinset S ↔
      ∃ i, orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) i = p := by
  classical
  simp [orderedSimplexFinset]

private theorem orderedSimplexPunctured_subset (S : CyclicStaircase) (g : Point3)
    (hord : PairCountsOrdered S) :
    orderedSimplexPunctured S g ⊆ puncturedFullCoreFinset S g := by
  classical
  intro p hp
  have hpf := (Finset.mem_filter.mp hp)
  obtain ⟨i, rfl⟩ := (mem_orderedSimplexFinset S p).mp hpf.1
  exact (mem_puncturedFullCoreFinset S g _).mpr
    ⟨orderedSimplex_fullCore S hord i, hpf.2⟩

theorem full_puncturedSimplex_budget (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) :
    fullM S + (orderedSimplexPunctured S g).card ≤ S.m := by
  have haccount := full_resource_accounting S hg hfull
  have hsub := Finset.card_le_card (orderedSimplexPunctured_subset S g hord)
  omega

theorem simplexCard_le_punctured_add_hole (S : CyclicStaircase) (g : Point3)
    (hord : PairCountsOrdered S) :
    simplexCard (pair13Count S.D) (pair23Count S.D) ≤
      (orderedSimplexPunctured S g).card + (coreHoleFinset S g).card := by
  classical
  let inside := (orderedSimplexFinset S).filter fun p => g ≤ p
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := orderedSimplexFinset S) (p := fun p : Point3 => g ≤ p)
  have hinside : inside ⊆ coreHoleFinset S g := by
    intro p hp
    have hpf := Finset.mem_filter.mp hp
    obtain ⟨i, rfl⟩ := (mem_orderedSimplexFinset S p).mp hpf.1
    exact (mem_coreHoleFinset S g _).mpr
      ⟨orderedSimplex_fullCore S hord i, hpf.2⟩
  have hc := Finset.card_le_card hinside
  have hpunct : (orderedSimplexFinset S).filter (fun p => ¬ g ≤ p) =
      orderedSimplexPunctured S g := by rfl
  rw [card_orderedSimplexFinset, hpunct] at hpartition
  dsimp [inside] at hc
  omega

theorem full_simplex_hole_budget (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) :
    fullM S + simplexCard (pair13Count S.D) (pair23Count S.D) ≤
      S.m + (coreHoleFinset S g).card := by
  have hb := full_puncturedSimplex_budget S hg hfull hord
  have hs := simplexCard_le_punctured_add_hole S g hord
  omega

theorem full_simplex_largeHole_budget (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) :
    fullM S + simplexCard (pair13Count S.D) (pair23Count S.D) ≤
      S.m + largeHoleCap (pair23Count S.D) := by
  have hb := full_simplex_hole_budget S hg hfull hord
  have hh := coreHole_card_le_largeHoleCap S hg hfull hord
  omega

end NSP3
