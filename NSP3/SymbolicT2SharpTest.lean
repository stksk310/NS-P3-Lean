import NSP3.SymbolicT2Sharp
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hA : 2≤g.x) (hp : (g.y=1 ∧ 2≤g.z) ∨ (g.z=1 ∧ 2≤g.y)) : fullTarget S≤S.m :=
  fullSupport_t2_transverse_unit_sharp S hg hf ho ht hA hp
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hx : g.x=1) (hp : g.y=1 ∨ g.z=1) : fullTarget S≤S.m :=
  fullSupport_t2_two_transverse_units_sharp S hg hf ho ht hx hp
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2≤pair13Count S.D) (hne : g.y≠1 ∨ g.z≠1) : fullTarget S≤S.m :=
  fullSupport_t2_non_h11_symbolic_sharp S hg hf ho ht hs hne
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2) : fullTarget S≤S.m :=
  fullSupport_t2_ordered_symbolic_sharp S hg hf ho ht
-- These universal contracts impose no unit-weight or primitive-g hypothesis.
example (S : CyclicStaircase)
    (hg : MinimalComplement S.D (Point3.mk 2 2 2))
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2) : fullTarget S≤S.m :=
  fullSupport_t2_no_unit_sharp S hg (by norm_num [FullSupport]) ho ht (by decide) (by decide) (by decide)
example (S : CyclicStaircase)
    (hg : MinimalComplement S.D (Point3.mk 2 2 1))
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (_hr : pair12Count S.D=3) (_hs : pair13Count S.D=3) : fullTarget S≤S.m :=
  fullSupport_t2_transverse_unit_sharp S hg (by norm_num [FullSupport]) ho ht (by decide) (Or.inr ⟨rfl,by decide⟩)
example (S : CyclicStaircase)
    (hg : MinimalComplement S.D (Point3.mk 2 1 2))
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (_hr : pair12Count S.D=3) (_hs : pair13Count S.D=3) : fullTarget S≤S.m :=
  fullSupport_t2_transverse_unit_sharp S hg (by norm_num [FullSupport]) ho ht (by decide) (Or.inl ⟨rfl,by decide⟩)
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (_he : S.m=fullTarget S) : fullTarget S≤S.m :=
  fullSupport_t2_ordered_symbolic_sharp S hg hf ho ht
end NSP3
