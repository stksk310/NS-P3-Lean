import NSP3.SymbolicThin23Endpoint
namespace NSP3
open Finset

-- Off-by-one controls: both actual height formulas are checked against literals.
example (S : CyclicStaircase) (g : Point3)
    (hr : pair12Count S.D=5) (hs : pair13Count S.D=4) (hh : g.x=5) :
    thin23ColumnHeight S g (Point3.mk 0 1 2)=2 ∧
      thin23ColumnHeight S g (Point3.mk 0 2 1)=3 := by
  norm_num [thin23ColumnHeight,hr,hs,hh]

-- All-zero columns are allowed; they never earn fictitious positive cardinality.
example (S : CyclicStaircase) (g : Point3)
    (hr : pair12Count S.D=2) (hs : pair13Count S.D=2) (hh : g.x=2) :
    thin23Column S g (Point3.mk 0 1 2)=∅ ∧
      thin23Column S g (Point3.mk 0 2 1)=∅ := by
  simp [thin23Column,thin23ColumnHeight,hr,hs,hh]

-- A bogus extra-base outside D is rejected, not lifted on numeric data alone.
example (S : CyclicStaircase) (g p : Point3) (hp : p ∉ S.D) :
    p ∉ thin23ColumnBases S g := by
  classical
  intro hb
  exact hp ((mem_pair23ExtraFinset S p).mp (mem_filter.mp hb).1).1

-- Full-support columns cannot be confused with a positive pair face.
example (S : CyclicStaircase) (g : Point3) :
    Disjoint (thin23LiftedColumns S g) (plane12PosFinset S) := by
  classical
  apply disjoint_left.mpr
  intro p hp hq
  have hf := thin23_lifted_columns_fullSupport S g hp
  have hpz : 0 < p.z := hf.2.2
  have hzero := ((mem_plane12PosFinset S p).mp hq).2.2.2
  omega

-- Accidental core/box overlap is excluded by an actual disjointness theorem.
example (S : CyclicStaircase) (g : Point3) :
    thin23LiftedColumns S g ∩ fullSupportSymbolicH S g=∅ := by
  classical
  exact disjoint_iff_inter_eq_empty.mp (thin23_lifted_columns_disjoint_H S g)

-- Dropping the complete residue model is invalid: this 10-point downset has
-- g=111 as a full hole and only the point 011 on its positive yz face.
private def incompleteSeed : Finset Point3 :=
  {Point3.mk 0 0 0,Point3.mk 1 0 0,Point3.mk 2 0 0,
   Point3.mk 0 1 0,Point3.mk 0 2 0,Point3.mk 0 0 1,Point3.mk 0 0 2,
   Point3.mk 1 1 0,Point3.mk 1 0 1,Point3.mk 0 1 1}
example : incompleteSeed.card=10 := by decide
example : MinimalComplement incompleteSeed (Point3.mk 1 1 1) := by
  norm_num [MinimalComplement,incompleteSeed,Point3.pred1,Point3.pred2,Point3.pred3]
example : incompleteSeed.filter (fun p => p.x=0 ∧ 0<p.y ∧ 0<p.z)=
    {Point3.mk 0 1 1} := by decide
example : Point3.mk 0 1 2 ∉ incompleteSeed ∧ Point3.mk 0 2 1 ∉ incompleteSeed := by decide

-- Pure arithmetic near the balanced boundary, hand-computed expected values.
example : ((3+2+4)^2+3)/4 ≤ Nat.choose 3 2+Nat.choose 2 2+4*3+3+3 := by decide
example : ((3+3+4)^2+3)/4 ≤ Nat.choose 3 2+Nat.choose 3 2+4*4+3+3 := by decide
end NSP3
