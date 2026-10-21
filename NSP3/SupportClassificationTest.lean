import NSP3.SupportClassification

namespace NSP3

example (S : CyclicStaircase) : Point3.zero ∈ S.D := S.zero_mem

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b) :
    Pure1 b ∨ Pure2 b ∨ Pure3 b ∨ Pair12 b ∨ Pair13 b ∨ Pair23 b ∨ FullSupport b :=
  minimalComplement_support_cases S hb

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b) :
    ∃! k : SupportKind, HasSupportKind k b :=
  minimalComplement_supportKind_unique S hb

example (b : Point3) (h : Pure1 b) : HasSupportKind .pure1 b := h
example (b : Point3) (h : Pure2 b) : HasSupportKind .pure2 b := h
example (b : Point3) (h : Pure3 b) : HasSupportKind .pure3 b := h
example (b : Point3) (h : Pair12 b) : HasSupportKind .pair12 b := h
example (b : Point3) (h : Pair13 b) : HasSupportKind .pair13 b := h
example (b : Point3) (h : Pair23 b) : HasSupportKind .pair23 b := h
example (b : Point3) (h : FullSupport b) : HasSupportKind .full b := h

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) {g : Point3}
    (hg : MinimalComplement S.D g) : ¬ FullSupport g :=
  hnf.not_full hg

example (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (h12 : Pair12 b)
    (hc : MinimalComplement S.D c) (h13 : Pair13 c) :
    S.rho b ≠ S.rho c :=
  pair12_pair13_returns_ne S hb h12 hc h13

example (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (h12 : Pair12 b)
    (hc : MinimalComplement S.D c) (h23 : Pair23 c) :
    S.rho b ≠ S.rho c :=
  pair12_pair23_returns_ne S hb h12 hc h23

example (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (h13 : Pair13 b)
    (hc : MinimalComplement S.D c) (h23 : Pair23 c) :
    S.rho b ≠ S.rho c :=
  pair13_pair23_returns_ne S hb h13 hc h23

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) :
    (zeroReturningPairBoundaries S).card ≤ 1 :=
  zeroReturningPairBoundaries_card_le_one S hnf

end NSP3
