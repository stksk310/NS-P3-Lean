import NSP3.SymbolicThreePlaneBudget

open NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullSupportSymbolicBW S g ≤ S.m := fullSupport_symbolic_BW_lower S hg hf ho

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullSupportSymbolicBF S g ≤ S.m := fullSupport_symbolic_BF_lower S hg hf ho

-- Empty W ranges and r=0/1 are not silently excluded.
example : ferrersW 0 1 1 = 0 := by decide
example : ferrersW 1 1 1 = 0 := by decide
example : ferrersW 4 2 2 = 4 := by decide
example : (ferrersRectangle 0 1 1).card = 1 := by decide
example : ferrersPlaneDefect 3 2 2 = 1 := by decide
example : rankCutPhi 3 2 2 = 2 := by decide
example : max (ferrersPlaneDefect 3 2 2) (rankCutPhi 3 2 2) = 2 := by decide
example (r A B : ℕ) (ha : 0<A) (hb : 0<B) :
    1 ≤ max (ferrersW r A B) (rankCutPhi r A B) := ferrers_strict_gain r A B ha hb
