import NSP3.SymbolicTerminalRectangle
namespace NSP3
-- General high corners, not an exact triangular plane/adjacent-only block.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (b c : Pair12Boundary S)
    (hbx : g.x ≤ b.val.x) (hby : g.y ≤ b.val.y)
    (hcx : g.x ≤ c.val.x) (hcy : g.y ≤ c.val.y)
    (horder : b.val.x < c.val.x) :
    g.x < c.val.x-b.val.x ∨ g.y < b.val.y-c.val.y :=
  pair12_terminal_rectangle_separation S hg hf b c hbx hby hcx hcy horder
end NSP3
