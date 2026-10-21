import NSP3.SymbolicFerrersRank
namespace NSP3
-- Hand-derived first exterior diagonal, zero-corner rectangle, and endpoints.
#check rankCutPhi_first_diagonal
example : rankCutPhi 0 2 3 = 6 := by decide
example : rankCutPhi 3 2 2 = 2 := by decide
example : rankCutPhi 2 1 1 = 0 := by decide
example : rankCutPhi 4 2 3 = 2 := by decide
example : rankCutPhi 3 2 2 ≠ 3 := by decide
end NSP3
