import NSP3.SymbolicFerrersPlane13
import NSP3.SymbolicFerrersPlane23

open NSP3
example (S : CyclicStaircase) {A B : ℕ} (ha : 0<A) (hb : 0<B)
    (hm : Point3.mk A 0 B ∈ S.D) :
    Nat.choose (pair13Count S.D) 2+rankCutPhi (pair13Count S.D) A B ≤
      (plane13PosFinset S).card := Ferrers13.pair_plane_face_rank_lower S ha hb hm

example (S : CyclicStaircase) {A B : ℕ} (ha : 0<A) (hb : 0<B)
    (hm : Point3.mk 0 A B ∈ S.D) :
    Nat.choose (pair23Count S.D) 2+rankCutPhi (pair23Count S.D) A B ≤
      (plane23PosFinset S).card := Ferrers23.pair_plane_face_rank_lower S ha hb hm

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (Finset.Icc g.x (pair13Count S.D-g.z)).sum
      (fun i => min (g.x*(pair13Count S.D-i)) (g.z*i)) ≤
      (pair13ExtraFinset S).card := Ferrers13.pair13_weighted_gap_lower S hg hf

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (Finset.Icc g.y (pair23Count S.D-g.z)).sum
      (fun i => min (g.y*(pair23Count S.D-i)) (g.z*i)) ≤
      (pair23ExtraFinset S).card := Ferrers23.pair23_weighted_gap_lower S hg hf
