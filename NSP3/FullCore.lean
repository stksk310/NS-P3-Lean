import NSP3.ProjectionLifting
import NSP3.ThreePlaneBound

namespace NSP3

def FullCore (S : CyclicStaircase) (p : Point3) : Prop :=
  0 < p.x ∧ 0 < p.y ∧ 0 < p.z ∧
    p.x + p.y ≤ pair12Count S.D ∧
    p.x + p.z ≤ pair13Count S.D ∧
    p.y + p.z ≤ pair23Count S.D

theorem noFull_fullCore_mem (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) {p : Point3} (hcore : FullCore S p) :
    p ∈ S.D := by
  have h12 : proj12 p ∈ S.D := by
    simpa [proj12] using pair12Triangle_subset S.down_closed
      hcore.1 hcore.2.1 hcore.2.2.2.1
  have h13 : proj13 p ∈ S.D := by
    simpa [proj13] using pair13Triangle_subset S.down_closed
      hcore.1 hcore.2.2.1 hcore.2.2.2.2.1
  have h23 : proj23 p ∈ S.D := by
    simpa [proj23] using pair23Triangle_subset S.down_closed
      hcore.2.1 hcore.2.2.1 hcore.2.2.2.2.2
  exact noFull_projection_lifting S hnf p hcore.1 hcore.2.1 hcore.2.2.1 h12 h13 h23

noncomputable def fullCoreBound (S : CyclicStaircase) : ℕ :=
  pair12Count S.D + pair13Count S.D + pair23Count S.D + 1

noncomputable def fullCoreFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  let triples := (Finset.range (fullCoreBound S)).product
    ((Finset.range (fullCoreBound S)).product (Finset.range (fullCoreBound S)))
  exact (triples.image fun a => Point3.mk a.1 a.2.1 a.2.2).filter (FullCore S)

@[simp] theorem mem_fullCoreFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ fullCoreFinset S ↔ FullCore S p := by
  classical
  constructor
  · exact fun hp => (Finset.mem_filter.mp hp).2
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hp⟩
    apply Finset.mem_image.mpr
    refine ⟨(p.x, (p.y, p.z)), ?_, rfl⟩
    apply Finset.mem_product.mpr
    rcases hp with ⟨hx, hy, hz, h12, h13, h23⟩
    constructor
    · apply Finset.mem_range.mpr
      unfold fullCoreBound
      omega
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        change p.y < fullCoreBound S
        unfold fullCoreBound
        omega
      · apply Finset.mem_range.mpr
        change p.z < fullCoreBound S
        unfold fullCoreBound
        omega

theorem fullSupport_of_mem_fullCoreFinset {S : CyclicStaircase} {p : Point3}
    (hp : p ∈ fullCoreFinset S) : FullSupport p := by
  have h := (mem_fullCoreFinset S p).mp hp
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem fullCoreFinset_subset_D (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) : fullCoreFinset S ⊆ S.D := by
  intro p hp
  exact noFull_fullCore_mem S hnf ((mem_fullCoreFinset S p).mp hp)

theorem fullCore_card_lower (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) : (fullCoreFinset S).card ≤ S.D.card :=
  Finset.card_le_card (fullCoreFinset_subset_D S hnf)

theorem threePlaneSourcePoint_not_fullSupport (S : CyclicStaircase)
    (a : ThreePlaneSource S) : ¬ FullSupport (threePlaneSourcePoint S a) := by
  rcases a with _ | a
  · simp [threePlaneSourcePoint, FullSupport]
  · rcases a with _ | a
    · simp [threePlaneSourcePoint, FullSupport]
    · rcases a with _ | a
      · simp [threePlaneSourcePoint, FullSupport]
      · rcases a with _ | a
        · simp [threePlaneSourcePoint, FullSupport]
        · rcases a with _ | a
          · simp [threePlaneSourcePoint, FullSupport]
          · rcases a with _ | a <;> simp [threePlaneSourcePoint, FullSupport]

def ThreePlaneFullCoreSource (S : CyclicStaircase) :=
  ThreePlaneSource S ⊕ {p : Point3 // p ∈ fullCoreFinset S}

noncomputable instance (S : CyclicStaircase) : Fintype (ThreePlaneFullCoreSource S) := by
  unfold ThreePlaneFullCoreSource
  let _ : Fintype {p : Point3 // p ∈ fullCoreFinset S} := Fintype.ofFinite _
  infer_instance

def threePlaneFullCorePoint (S : CyclicStaircase) : ThreePlaneFullCoreSource S → Point3
  | .inl a => threePlaneSourcePoint S a
  | .inr p => p.1

theorem threePlaneFullCorePoint_injective (S : CyclicStaircase) :
    Function.Injective (threePlaneFullCorePoint S) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          apply congrArg Sum.inl
          exact threePlaneSourcePoint_injective S h
      | inr b =>
          have hfull := fullSupport_of_mem_fullCoreFinset b.2
          change threePlaneSourcePoint S a = b.1 at h
          have : FullSupport (threePlaneSourcePoint S a) := h ▸ hfull
          exact False.elim ((threePlaneSourcePoint_not_fullSupport S a) this)
  | inr a =>
      cases b with
      | inl b =>
          have hfull := fullSupport_of_mem_fullCoreFinset a.2
          change a.1 = threePlaneSourcePoint S b at h
          have : FullSupport (threePlaneSourcePoint S b) := h.symm ▸ hfull
          exact False.elim ((threePlaneSourcePoint_not_fullSupport S b) this)
      | inr b =>
          apply congrArg Sum.inr
          exact Subtype.ext h

theorem threePlane_fullCore_card_lower (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) :
    pure1Intercept S + pure2Intercept S + pure3Intercept S - 2
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card ≤ S.D.card := by
  classical
  let target := {p : Point3 // p ∈ S.D}
  let f : ThreePlaneFullCoreSource S → target := fun a =>
    match a with
    | .inl s => ⟨threePlaneSourcePoint S s, threePlaneSourcePoint_mem S s⟩
    | .inr p => ⟨p.1, fullCoreFinset_subset_D S hnf p.2⟩
  have hf : Function.Injective f := by
    intro a b h
    apply threePlaneFullCorePoint_injective S
    have hv := congrArg (fun x : target => x.1) h
    cases a <;> cases b <;> exact hv
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card target = S.D.card := by simp [target]
  have hsource : Fintype.card (ThreePlaneFullCoreSource S) =
      Fintype.card (ThreePlaneSource S) + (fullCoreFinset S).card := by
    simp [ThreePlaneFullCoreSource]
  rw [hsource, card_threePlaneSource, htarget] at hcard
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

end NSP3
