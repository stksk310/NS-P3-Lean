import NSP3.V03.CornerBound

namespace NSP3.V03
open Finset

#check planar_births_le_oriented
#check planar_maxima_le_x_corners
#check maximal_card_le_oriented_layers
#check globalOriented_card_eq_layers
#check maximalPoints_card_add_two_le_boundary
#check maximalPoints_card_add_two_le_boundary_natCard

#print axioms planar_births_le_oriented
#print axioms globalOriented_card_eq_layers
#print axioms maximalPoints_card_add_two_le_boundary
#print axioms maximalPoints_card_add_two_le_boundary_natCard

-- Empty slices have boundary {0}, but the origin has no paid orientation.
example (E : Finset Point3) : orientedCorners E ∅=∅ := by
  classical
  ext ⟨b,i⟩
  cases i <;> simp [orientedCorners,cornerBoundary_empty,Point3.zero] <;>
    rintro rfl _ <;> rfl

-- The nonempty hypothesis in the final +2 inequality is indispensable.
example : ¬ ((maximalPoints ∅).card+2≤
    (cornerBoundary ∅).card+(fullSupportCorners ∅).card) := by
  classical
  have hm : maximalPoints ∅=∅ := by ext p; simp [mem_maximalPoints]
  have hf : fullSupportCorners ∅=∅ := by
    simp [fullSupportCorners,cornerBoundary_empty,FullSupport,Point3.zero]
  rw [hm,hf,cornerBoundary_empty]
  norm_num

end NSP3.V03
