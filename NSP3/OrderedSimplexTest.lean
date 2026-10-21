import NSP3.OrderedSimplex

namespace NSP3

example : simplexCard 0 0 = 0 := by norm_num [simplexCard]
example : simplexCard 1 1 = 0 := by norm_num [simplexCard]
example : simplexCard 2 2 = 1 := by norm_num [simplexCard]
example : simplexCard 3 2 = 2 := by norm_num [simplexCard]
example : simplexCard 3 3 = 4 := by norm_num [simplexCard]

example (s t : ℕ) :
    Fintype.card (OrderedSimplexSource s t) = simplexCard s t :=
  card_orderedSimplexSource s t

example (s t : ℕ) (hst : t ≤ s) (i : OrderedSimplexSource s t) :
    OrderedSimplex s t (orderedSimplexPoint s t i) :=
  orderedSimplexPoint_mem s t hst i

example (s t : ℕ) : Function.Injective (orderedSimplexPoint s t) :=
  orderedSimplexPoint_injective s t

example (S : CyclicStaircase) (hord : PairCountsOrdered S)
    (i : OrderedSimplexSource (pair13Count S.D) (pair23Count S.D)) :
    FullCore S (orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) i) :=
  orderedSimplex_fullCore S hord i

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (i : OrderedSimplexSource (pair13Count S.D) (pair23Count S.D)) :
    orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) i ∈ S.D :=
  noFull_orderedSimplex_mem S hnf hord i

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + simplexCard (pair13Count S.D) (pair23Count S.D) ≤ S.m :=
  m5_simplex_lower_equal S hnf hord heq

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + simplexCard (pair13Count S.D) (pair23Count S.D) ≤ S.m :=
  m5_simplex_lower_strict S hnf hord hlt

end NSP3
