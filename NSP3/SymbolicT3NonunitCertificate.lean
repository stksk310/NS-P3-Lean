import NSP3.Residue

namespace NSP3

/-- Residues of a finite, explicitly forced geometric subset. -/
def t3SmallResidues (m : ℕ) (a b c : Fin m) (P : List Point3) : List (ZMod m) :=
  P.map (residueOf (a.val : ZMod m) (b.val : ZMod m) (c.val : ZMod m))

/-- The punctured box, pure axes and forced triangles; not a staircase atlas. -/
def t3r3NonunitPoints : List Point3 :=
  [⟨0,0,0⟩,
   ⟨0,0,1⟩,
   ⟨0,0,2⟩,
   ⟨0,0,3⟩,
   ⟨0,1,0⟩,
   ⟨0,1,1⟩,
   ⟨0,1,2⟩,
   ⟨0,2,0⟩,
   ⟨0,2,1⟩,
   ⟨0,2,2⟩,
   ⟨0,3,0⟩,
   ⟨1,0,0⟩,
   ⟨1,0,1⟩,
   ⟨1,0,2⟩,
   ⟨1,1,0⟩,
   ⟨1,1,1⟩,
   ⟨1,1,2⟩,
   ⟨1,2,0⟩,
   ⟨1,2,1⟩,
   ⟨1,2,2⟩,
   ⟨2,0,0⟩,
   ⟨2,0,1⟩,
   ⟨2,0,2⟩,
   ⟨2,1,0⟩,
   ⟨2,1,1⟩,
   ⟨2,1,2⟩,
   ⟨2,2,0⟩,
   ⟨2,2,1⟩,
   ⟨3,0,0⟩]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t3r3NonunitPoints_collision_29 : ∀ a b c : Fin 29,
    (2*(a.val : ZMod 29)+2*(b.val : ZMod 29)+2*(c.val : ZMod 29)=0) →
    ¬ (t3SmallResidues 29 a b c t3r3NonunitPoints).Nodup := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t3r3NonunitPoints_collision_30 : ∀ a b c : Fin 30,
    (2*(a.val : ZMod 30)+2*(b.val : ZMod 30)+2*(c.val : ZMod 30)=0) →
    ¬ (t3SmallResidues 30 a b c t3r3NonunitPoints).Nodup := by decide

/-- The punctured box, pure axes and forced triangles; not a staircase atlas. -/
def t3r4NonunitPoints : List Point3 :=
  [⟨0,0,0⟩,
   ⟨0,0,1⟩,
   ⟨0,0,2⟩,
   ⟨0,0,3⟩,
   ⟨0,0,4⟩,
   ⟨0,1,0⟩,
   ⟨0,1,1⟩,
   ⟨0,1,2⟩,
   ⟨0,2,0⟩,
   ⟨0,2,1⟩,
   ⟨0,2,2⟩,
   ⟨0,3,0⟩,
   ⟨0,4,0⟩,
   ⟨1,0,0⟩,
   ⟨1,0,1⟩,
   ⟨1,0,2⟩,
   ⟨1,0,3⟩,
   ⟨1,1,0⟩,
   ⟨1,1,1⟩,
   ⟨1,1,2⟩,
   ⟨1,2,0⟩,
   ⟨1,2,1⟩,
   ⟨1,2,2⟩,
   ⟨1,3,0⟩,
   ⟨2,0,0⟩,
   ⟨2,0,1⟩,
   ⟨2,0,2⟩,
   ⟨2,1,0⟩,
   ⟨2,1,1⟩,
   ⟨2,1,2⟩,
   ⟨2,2,0⟩,
   ⟨2,2,1⟩,
   ⟨2,2,2⟩,
   ⟨3,0,0⟩,
   ⟨3,0,1⟩,
   ⟨3,0,2⟩,
   ⟨3,1,0⟩,
   ⟨3,1,1⟩,
   ⟨3,1,2⟩,
   ⟨3,2,0⟩,
   ⟨3,2,1⟩,
   ⟨4,0,0⟩]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t3r4NonunitPoints_collision_42 : ∀ a b c : Fin 42,
    (3*(a.val : ZMod 42)+2*(b.val : ZMod 42)+2*(c.val : ZMod 42)=0) →
    ¬ (t3SmallResidues 42 a b c t3r4NonunitPoints).Nodup := by decide

end NSP3

