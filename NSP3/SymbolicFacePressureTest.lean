import NSP3.SymbolicFacePressure
namespace NSP3
-- No full-support or residue unit hypothesis: any actual standard face suffices.
example (S : CyclicStaircase) {A B : ℕ} (hm : Point3.mk A B 0 ∈ S.D) :
    pair12Count S.D + A + B ≤ (pure1Intercept S-1)+(pure2Intercept S-1) :=
  pair12_face_axis_pressure S hm
#check pair13_face_axis_pressure
#check pair23_face_axis_pressure
end NSP3
