import NSP3.Residue

namespace NSP3

/-- Only geometrically forced standard points of the q333/g221 endpoint. -/
def t3UnitZForcedPoints : List Point3 :=
  [⟨0,0,0⟩,⟨1,0,0⟩,⟨2,0,0⟩,⟨3,0,0⟩,
   ⟨0,1,0⟩,⟨0,2,0⟩,⟨0,3,0⟩,⟨0,0,1⟩,⟨0,0,2⟩,⟨0,0,3⟩,
   ⟨1,1,0⟩,⟨1,2,0⟩,⟨2,1,0⟩,⟨1,0,1⟩,⟨1,0,2⟩,⟨2,0,1⟩,
   ⟨0,1,1⟩,⟨0,1,2⟩,⟨0,2,1⟩,⟨2,2,0⟩,
   ⟨1,1,1⟩,⟨1,1,2⟩,⟨1,2,1⟩,⟨2,1,1⟩]

def t3UnitZEndpointResidues (m : ℕ) (a b : Fin m) : List (ZMod m) :=
  t3UnitZForcedPoints.map (residueOf (a.val : ZMod m) (b.val : ZMod m)
    (-2*(a.val : ZMod m)-2*(b.val : ZMod m)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Single endpoint, all residue weights, ordinary kernel reduction; no 203-slice checker. -/
theorem t3_unit_z_endpoint_collision_30 :
    ∀ a b : Fin 30, ¬ (t3UnitZEndpointResidues 30 a b).Nodup := by decide

end NSP3
