import NSP3.SymbolicBWCompletion

namespace NSP3
namespace SymbolicCoordinates

/-- false exchanges x/y; true exchanges y/z. These generate all permutations. -/
def swap (b : Bool) (q : Point3) : Point3 :=
  if b then ⟨q.x,q.z,q.y⟩ else ⟨q.y,q.x,q.z⟩

@[simp] private theorem swap_swap (b : Bool) (q : Point3) :
    swap b (swap b q)=q := by cases b <;> rfl

private theorem swap_injective (b : Bool) : Function.Injective (swap b) := by
  intro p q h
  simpa only [swap_swap] using congrArg (swap b) h

def swapSet (b : Bool) (D : Finset Point3) : Finset Point3 := D.image (swap b)

@[simp] private theorem mem_swapSet (b : Bool) (D : Finset Point3) (q : Point3) :
    q ∈ swapSet b D ↔ swap b q ∈ D := by
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    simpa only [swap_swap] using hp
  · intro h
    exact Finset.mem_image.mpr ⟨swap b q,h,swap_swap b q⟩

private theorem minimal_swap (b : Bool) (D : Finset Point3) (q : Point3) :
    MinimalComplement (swapSet b D) q ↔ MinimalComplement D (swap b q) := by
  cases b <;>
    simp only [MinimalComplement,mem_swapSet,swap,Bool.false_eq_true,ite_false,ite_true,
      Point3.pred1,Point3.pred2,Point3.pred3] <;> tauto

private theorem full_swap (b : Bool) (q : Point3) :
    FullSupport (swap b q) ↔ FullSupport q := by
  cases b <;> simp [FullSupport,swap] <;> tauto

/-- The residue equivalence is transported, not assumed anew. -/
noncomputable def staircase (b : Bool) (S : CyclicStaircase) : CyclicStaircase where
  m := S.m
  hm := S.hm
  D := swapSet b S.D
  down_closed := by
    intro a c hac hc
    rw [mem_swapSet] at hc ⊢
    apply S.down_closed ?_ hc
    cases b
    · exact ⟨hac.2.1,hac.1,hac.2.2⟩
    · exact ⟨hac.1,hac.2.2,hac.2.1⟩
  p1 := if b then S.p1 else S.p2
  p2 := if b then S.p3 else S.p1
  p3 := if b then S.p2 else S.p3
  residueEquiv := (show {q // q ∈ swapSet b S.D} ≃ {q // q ∈ S.D} from
    { toFun := fun q => ⟨swap b q.1,(mem_swapSet b S.D q.1).mp q.2⟩
      invFun := fun q => ⟨swap b q.1,(mem_swapSet b S.D (swap b q.1)).mpr (by simpa only [swap_swap] using q.2)⟩
      left_inv := by intro q; apply Subtype.ext; exact swap_swap b q.1
      right_inv := by intro q; apply Subtype.ext; exact swap_swap b q.1 }).trans S.residueEquiv
  residueEquiv_spec := by
    intro q
    change S.residueEquiv ⟨swap b q.1,_⟩ = _
    rw [S.residueEquiv_spec]
    cases b <;> simp [swap,residueOf] <;> ring

private theorem counts (b : Bool) (S : CyclicStaircase) :
    pair12Count (staircase b S).D=(if b then pair13Count S.D else pair12Count S.D) ∧
    pair13Count (staircase b S).D=(if b then pair12Count S.D else pair23Count S.D) ∧
    pair23Count (staircase b S).D=(if b then pair23Count S.D else pair13Count S.D) := by
  classical
  have hc (F : Finset Point3) : (swapSet b F).card=F.card :=
    Finset.card_image_of_injective F (swap_injective b)
  cases b
  · have h12 : pair12Boundaries (swapSet false S.D)=swapSet false (pair12Boundaries S.D) := by
      ext q
      simp only [mem_pair12Boundaries,mem_swapSet,minimal_swap]
      simp [Pair12,swap,and_comm,and_left_comm,and_assoc]
    have h13 : pair13Boundaries (swapSet false S.D)=swapSet false (pair23Boundaries S.D) := by
      ext q
      simp only [mem_pair13Boundaries,mem_swapSet,mem_pair23Boundaries,minimal_swap]
      simp [Pair13,Pair23,swap,and_comm,and_left_comm,and_assoc]
    have h23 : pair23Boundaries (swapSet false S.D)=swapSet false (pair13Boundaries S.D) := by
      ext q
      simp only [mem_pair23Boundaries,mem_swapSet,mem_pair13Boundaries,minimal_swap]
      simp [Pair13,Pair23,swap,and_comm,and_left_comm,and_assoc]
    change (pair12Boundaries (swapSet false S.D)).card=_ ∧
      (pair13Boundaries (swapSet false S.D)).card=_ ∧ (pair23Boundaries (swapSet false S.D)).card=_
    simp only [h12,h13,h23,hc,pair12Count,pair13Count,pair23Count,Bool.false_eq_true,ite_false]
    simp
  · have h12 : pair12Boundaries (swapSet true S.D)=swapSet true (pair13Boundaries S.D) := by
      ext q
      simp only [mem_pair12Boundaries,mem_swapSet,mem_pair13Boundaries,minimal_swap]
      simp [Pair12,Pair13,swap,and_comm,and_left_comm,and_assoc]
    have h13 : pair13Boundaries (swapSet true S.D)=swapSet true (pair12Boundaries S.D) := by
      ext q
      simp only [mem_pair13Boundaries,mem_swapSet,mem_pair12Boundaries,minimal_swap]
      simp [Pair12,Pair13,swap,and_comm,and_left_comm,and_assoc]
    have h23 : pair23Boundaries (swapSet true S.D)=swapSet true (pair23Boundaries S.D) := by
      ext q
      simp only [mem_pair23Boundaries,mem_swapSet,minimal_swap]
      simp [Pair23,swap,and_comm,and_assoc]
    change (pair12Boundaries (swapSet true S.D)).card=_ ∧
      (pair13Boundaries (swapSet true S.D)).card=_ ∧ (pair23Boundaries (swapSet true S.D)).card=_
    simp only [h12,h13,h23,hc,pair12Count,pair13Count,pair23Count,ite_true]
    simp

private theorem target (b : Bool) (S : CyclicStaircase) :
    fullTarget (staircase b S)=fullTarget S := by
  have h := counts b S
  unfold fullTarget
  rw [h.1,h.2.1,h.2.2]
  congr 1
  cases b <;> simp <;> omega

private def Sharp (S : CyclicStaircase) : Prop :=
  ∀ g, MinimalComplement S.D g → FullSupport g → fullTarget S ≤ S.m

private theorem pullback (b : Bool) (S : CyclicStaircase)
    (h : Sharp (staircase b S)) : Sharp S := by
  intro g hg hf
  have hg' : MinimalComplement (staircase b S).D (swap b g) :=
    (minimal_swap b S.D (swap b g)).mpr (by simpa only [swap_swap] using hg)
  have hp := h (swap b g) hg' ((full_swap b g).mpr hf)
  change fullTarget (staircase b S) ≤ S.m at hp
  rw [target] at hp
  exact hp

private theorem ordered_sharp (S : CyclicStaircase) (ho : PairCountsOrdered S) :
    Sharp S := fun _ hg hf => fullSupport_ordered_symbolic_sharp S hg hf ho

private theorem sort_reduction (P : CyclicStaircase → Prop)
    (pull : ∀ b S, P (staircase b S) → P S)
    (ordered : ∀ S, PairCountsOrdered S → P S) (S : CyclicStaircase) : P S := by
  have solve (T : CyclicStaircase) (hst : pair23Count T.D ≤ pair13Count T.D) : P T := by
    by_cases hrs : pair13Count T.D ≤ pair12Count T.D
    · exact ordered T ⟨hst,hrs⟩
    apply pull true T
    have hc := counts true T
    by_cases hrt : pair23Count T.D ≤ pair12Count T.D
    · apply ordered
      unfold PairCountsOrdered
      rw [hc.1,hc.2.1,hc.2.2]
      simp only [ite_true]
      omega
    · apply pull false (staircase true T)
      have hd := counts false (staircase true T)
      apply ordered
      unfold PairCountsOrdered
      rw [hd.1,hd.2.1,hd.2.2,hc.1,hc.2.1,hc.2.2]
      simp only [Bool.false_eq_true,ite_false,ite_true]
      omega
  by_cases hst : pair23Count S.D ≤ pair13Count S.D
  · exact solve S hst
  · apply pull false S
    apply solve
    have hc := counts false S
    rw [hc.2.1,hc.2.2]
    simp only [Bool.false_eq_true,ite_false]
    omega

private theorem sort_sharp (S : CyclicStaircase) : Sharp S :=
  sort_reduction Sharp pullback ordered_sharp S

private def NoFullSharp (S : CyclicStaircase) : Prop :=
  NoFullSupportBoundary S → noFullTarget S ≤ S.m

private theorem noFull_target (b : Bool) (S : CyclicStaircase) :
    noFullTarget (staircase b S)=noFullTarget S := by
  have h := counts b S
  unfold noFullTarget
  rw [h.1,h.2.1,h.2.2]
  congr 1
  cases b <;> simp <;> omega

private theorem noFull_pullback (b : Bool) (S : CyclicStaircase)
    (h : NoFullSharp (staircase b S)) : NoFullSharp S := by
  intro hnf
  have ht : NoFullSupportBoundary (staircase b S) := by
    rintro ⟨g,hg,hf⟩
    exact hnf ⟨swap b g,(minimal_swap b S.D g).mp hg,(full_swap b g).mpr hf⟩
  have hp := h ht
  change noFullTarget (staircase b S) ≤ S.m at hp
  rw [noFull_target] at hp
  exact hp

private theorem noFull_ordered (S : CyclicStaircase) (ho : PairCountsOrdered S) :
    NoFullSharp S := fun hnf => noFull_sharp_bound_ordered S hnf ho

private theorem noFull_sort (S : CyclicStaircase) : NoFullSharp S :=
  sort_reduction NoFullSharp noFull_pullback noFull_ordered S

end SymbolicCoordinates

/-- Full-support sharp bound without an ordered pair-count hypothesis.
This is a theorem about cyclic staircases, not yet a numerical-semigroup bridge. -/
theorem fullSupport_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) : fullTarget S ≤ S.m :=
  SymbolicCoordinates.sort_sharp S g hg hf

theorem noFull_symbolic_sharp (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) :
    noFullTarget S ≤ S.m := SymbolicCoordinates.noFull_sort S hnf

attribute [local instance] Classical.propDecidable

/-- The two proved branches combined; no numerical-semigroup assertion is made. -/
theorem cyclicStaircase_symbolic_sharp (S : CyclicStaircase) :
    (if ∃ g, MinimalComplement S.D g ∧ FullSupport g then fullTarget S else noFullTarget S) ≤ S.m := by
  split_ifs with h
  · obtain ⟨g,hg,hf⟩ := h
    exact fullSupport_symbolic_sharp S hg hf
  · exact noFull_symbolic_sharp S h

end NSP3
