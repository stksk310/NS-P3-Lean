import NSP3.FiniteTerminalCheck

namespace NSP3

#check checkerPair12Count
#check checkerPair13Count
#check checkerPair23Count
#check checkerPair12Count_eq
#check terminalMatches
#check actual_standardSet_terminalMatches

example : checkerPair12Count {Point3.zero, Point3.e1, Point3.e2} = 1 := by
  decide

end NSP3
