import NSP3.SymbolicAxisPressure
namespace NSP3
#check three_axis_pressure_lower
example : jointAxisGain 1 1 1 = 2 := by decide
example : jointAxisGain 4 0 0 = 4 := by decide
example : jointAxisGain 0 0 0 = 0 := by decide
example : jointAxisGain 1 1 1 ≠ 3 := by decide
end NSP3
