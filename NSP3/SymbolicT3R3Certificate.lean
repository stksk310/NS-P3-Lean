import NSP3.Residue

namespace NSP3

/-- Twenty-five geometrically forced standard points for the g311 endpoint. -/
def t3r3ForcedPoints : List Point3 :=
  [⟨0,0,0⟩,
   ⟨1,0,0⟩,
   ⟨0,1,0⟩,
   ⟨0,0,1⟩,
   ⟨2,0,0⟩,
   ⟨0,2,0⟩,
   ⟨0,0,2⟩,
   ⟨3,0,0⟩,
   ⟨0,3,0⟩,
   ⟨0,0,3⟩,
   ⟨1,1,0⟩,
   ⟨1,2,0⟩,
   ⟨2,1,0⟩,
   ⟨1,0,1⟩,
   ⟨1,0,2⟩,
   ⟨2,0,1⟩,
   ⟨0,1,1⟩,
   ⟨0,1,2⟩,
   ⟨0,2,1⟩,
   ⟨1,1,1⟩,
   ⟨2,1,1⟩,
   ⟨1,2,1⟩,
   ⟨1,1,2⟩,
   ⟨3,1,0⟩,
   ⟨3,0,1⟩]

/-- Finite congruence certificate for a single small endpoint, not the 203-slice checker. -/
def t3r3EndpointResidues (m : ℕ) (a b : Fin m) : List (ZMod m) :=
  t3r3ForcedPoints.map (residueOf (a.val : ZMod m) (b.val : ZMod m)
    (-3*(a.val : ZMod m)-(b.val : ZMod m)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t3r3_endpoint_residue_collision_27 :
    ∀ a b : Fin 27, ¬ (t3r3EndpointResidues 27 a b).Nodup := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t3r3_endpoint_residue_collision_28 :
    ∀ a b : Fin 28, ¬ (t3r3EndpointResidues 28 a b).Nodup := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t3r3_endpoint_residue_collision_29 :
    ∀ a b : Fin 29, ¬ (t3r3EndpointResidues 29 a b).Nodup := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t3r3_endpoint_residue_collision_30 :
    ∀ a b : Fin 30, ¬ (t3r3EndpointResidues 30 a b).Nodup := by decide

/-- The certificate covers all residues, not only unit weights. -/
theorem t3r3_endpoint_residue_collision (m : ℕ) (hlo : 27 ≤ m) (hhi : m ≤ 30)
    (a b : Fin m) : ¬ (t3r3EndpointResidues m a b).Nodup := by
  interval_cases m
  · exact t3r3_endpoint_residue_collision_27 a b
  · exact t3r3_endpoint_residue_collision_28 a b
  · exact t3r3_endpoint_residue_collision_29 a b
  · exact t3r3_endpoint_residue_collision_30 a b

end NSP3

