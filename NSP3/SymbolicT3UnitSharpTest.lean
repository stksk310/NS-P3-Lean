import NSP3.SymbolicT3UnitSharp

namespace NSP3

example (a b : Fin 30) : ¬ (t3UnitZEndpointResidues 30 a b).Nodup :=
  t3_unit_z_endpoint_collision_30 a b

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=2) (hy : g.y=2) (hz : g.z=1) : fullTarget S ≤ S.m :=
  fullSupport_t3_unit_z_r3_sharp S hg hf ho ht hr hx hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hz : g.z=1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    fullTarget S ≤ S.m := fullSupport_t3_one_unit_z_symbolic_sharp S hg hf ho ht hz hx hy

end NSP3
