import NSP3.SymbolicT3Classification
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (hY : 5≤pure2Intercept S) (hZ : 5≤pure3Intercept S)
    (hnot : Point3.mk 0 1 3 ∉ S.D) :
    Point3.mk 0 2 2 ∈ S.D ∧ Point3.mk 0 3 1 ∈ S.D ∧ Point3.mk 0 4 1 ∈ S.D :=
  t3_missing13_standard_points S hg hf ht hy hz hY hZ hnot
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (hY : 5≤pure2Intercept S) (hZ : 5≤pure3Intercept S)
    (hnot : Point3.mk 0 3 1 ∉ S.D) :
    Point3.mk 0 2 2 ∈ S.D ∧ Point3.mk 0 1 3 ∈ S.D ∧ Point3.mk 0 1 4 ∈ S.D :=
  t3_missing31_standard_points S hg hf ht hy hz hY hZ hnot
end NSP3
