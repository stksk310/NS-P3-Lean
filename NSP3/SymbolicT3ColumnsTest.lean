import NSP3.SymbolicT3Columns
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (he : pair12Count S.D=pair13Count S.D) (hh : g.x=pair12Count S.D)
    {u v x : ℕ} (hu : 0<u) (hv : 0<v) (hs : 3<u+v)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (hb : Point3.mk 0 u v ∈ S.D) (hx : 1≤x)
    (hxu : x≤pair12Count S.D-u) (hxv : x≤pair12Count S.D-v) :
    Point3.mk x u v ∈ S.D :=
  t3_balanced_lifted_column_mem S hg hf he hh hu hv hs ht hy hz hb hx hxu hxv
example (S : CyclicStaircase) {g : Point3}
    (he : pair12Count S.D=pair13Count S.D) (hh : g.x=pair12Count S.D)
    (hk : pair12Count S.D=4) : thin23ColumnHeight S g (Point3.mk 0 4 1)=0 := by
  rw [t3_balanced_column_height S he hh (by decide) (by decide),hk]
  decide
example (S : CyclicStaircase) {g : Point3}
    (he : pair12Count S.D=pair13Count S.D) (hh : g.x=pair12Count S.D)
    (hk : pair12Count S.D=4) : thin23ColumnHeight S g (Point3.mk 0 1 3)=1 := by
  rw [t3_balanced_column_height S he hh (by decide) (by decide),hk]
  decide
end NSP3
