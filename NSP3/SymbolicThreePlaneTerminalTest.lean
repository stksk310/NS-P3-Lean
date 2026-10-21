import NSP3.SymbolicThreePlaneTerminal

open NSP3
example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (b c : Pair13Boundary S)
    (hb : g.x ≤ b.val.x ∧ g.z ≤ b.val.z)
    (hc : g.x ≤ c.val.x ∧ g.z ≤ c.val.z) (ho : b.val.x < c.val.x) :
    g.x < c.val.x-b.val.x ∨ g.z < b.val.z-c.val.z :=
  pair13_terminal_rectangle_separation S hg hf b c hb.1 hb.2 hc.1 hc.2 ho

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (b c : Pair23Boundary S)
    (hb : g.y ≤ b.val.y ∧ g.z ≤ b.val.z)
    (hc : g.y ≤ c.val.y ∧ g.z ≤ c.val.z) (ho : b.val.y < c.val.y) :
    g.y < c.val.y-b.val.y ∨ g.z < b.val.z-c.val.z :=
  pair23_terminal_rectangle_separation S hg hf b c hb.1 hb.2 hc.1 hc.2 ho

-- The strict off-by-one is essential; equality in both dimensions is impossible.
example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (b c : Pair13Boundary S)
    (hb : g.x ≤ b.val.x ∧ g.z ≤ b.val.z)
    (hc : g.x ≤ c.val.x ∧ g.z ≤ c.val.z) (ho : b.val.x < c.val.x)
    (hd : c.val.x-b.val.x ≤ g.x) (he : b.val.z-c.val.z ≤ g.z) : False := by
  have h := pair13_terminal_rectangle_separation S hg hf b c hb.1 hb.2 hc.1 hc.2 ho
  omega

-- Universal contract remains valid with nonunit opposite weight and g.y=1.
example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (_hunit : ¬ IsUnit S.p2) (hy : g.y=1)
    (b : Pair13Boundary S) (hb : g.x ≤ b.val.x ∧ g.z ≤ b.val.z) :
    pair13ReturnCoord S b = pure2Intercept S-1 := by
  have h := pair13_high_return_bounds S hg hf b hb.1 hb.2
  omega

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (_hunit : ¬ IsUnit S.p1) (hx : g.x=1)
    (b : Pair23Boundary S) (hb : g.y ≤ b.val.y ∧ g.z ≤ b.val.z) :
    pair23ReturnCoord S b = pure1Intercept S-1 := by
  have h := pair23_high_return_bounds S hg hf b hb.1 hb.2
  omega
