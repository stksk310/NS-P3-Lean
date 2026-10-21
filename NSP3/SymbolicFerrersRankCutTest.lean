import NSP3.SymbolicFerrersRankCut
namespace NSP3.Ferrers

-- Adding a corner-shape assumption or weakening the geometric area target fails this test.
example (S : CyclicStaircase) (A B : ℕ) (hA : 0<A) (hB : 0<B)
    (hm : Point3.mk A B 0 ∈ S.D) :
    Nat.choose (pair12Count S.D) 2+rankCutPhi (pair12Count S.D) A B ≤
      (plane12PosFinset S).card := pair_plane_face_rank_lower S hA hB hm

end NSP3.Ferrers
