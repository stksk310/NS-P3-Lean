import NSP3.FullCore

namespace NSP3

def SimplexLayer (t : ℕ) := Fin (t - 1)

def OrderedSimplexSource (s t : ℕ) :=
  Σ u : Fin (t - 1), Fin (u.1 + 1) × Fin (s - (u.1 + 1))

noncomputable instance (s t : ℕ) : Fintype (OrderedSimplexSource s t) := by
  unfold OrderedSimplexSource
  infer_instance

def simplexCard (s t : ℕ) : ℕ :=
  ∑ u ∈ Finset.range (t - 1), (u + 1) * (s - (u + 1))

def orderedSimplexPoint (s t : ℕ) (i : OrderedSimplexSource s t) : Point3 :=
  ⟨i.2.2.1 + 1, i.2.1.1 + 1, i.1.1 + 2 - (i.2.1.1 + 1)⟩

def OrderedSimplex (s t : ℕ) (p : Point3) : Prop :=
  0 < p.x ∧ 0 < p.y ∧ 0 < p.z ∧
    p.y + p.z ≤ t ∧ p.x + p.y + p.z ≤ s + 1

theorem orderedSimplexPoint_mem (s t : ℕ) (hst : t ≤ s)
    (i : OrderedSimplexSource s t) :
    OrderedSimplex s t (orderedSimplexPoint s t i) := by
  have hult : i.1.1 < t - 1 := i.1.2
  have hylt : i.2.1.1 < i.1.1 + 1 := i.2.1.2
  have hxlt : i.2.2.1 < s - (i.1.1 + 1) := i.2.2.2
  have hts := hst
  unfold OrderedSimplex orderedSimplexPoint
  simp only
  omega

theorem orderedSimplexPoint_injective (s t : ℕ) :
    Function.Injective (orderedSimplexPoint s t) := by
  rintro ⟨iu, ia, ib⟩ ⟨ju, ja, jb⟩ h
  have hix : (orderedSimplexPoint s t ⟨iu, ia, ib⟩).x =
      (orderedSimplexPoint s t ⟨ju, ja, jb⟩).x :=
    congrArg Point3.x h
  have hiy : (orderedSimplexPoint s t ⟨iu, ia, ib⟩).y =
      (orderedSimplexPoint s t ⟨ju, ja, jb⟩).y :=
    congrArg Point3.y h
  have hiz : (orderedSimplexPoint s t ⟨iu, ia, ib⟩).z =
      (orderedSimplexPoint s t ⟨ju, ja, jb⟩).z :=
    congrArg Point3.z h
  have hilo : ia.1 + 1 ≤ iu.1 + 1 := by
    have := ia.2
    omega
  have hjlo : ja.1 + 1 ≤ ju.1 + 1 := by
    have := ja.2
    omega
  have hk : iu.1 = ju.1 := by
    unfold orderedSimplexPoint at hiy hiz
    simp only at hiy hiz
    omega
  have hku : iu = ju := Fin.ext hk
  subst ju
  have hia : ia = ja := by
    apply Fin.ext
    unfold orderedSimplexPoint at hiy
    simp only at hiy
    omega
  subst ja
  have hib : ib = jb := by
    apply Fin.ext
    unfold orderedSimplexPoint at hix
    simp only at hix
    omega
  subst jb
  rfl

@[simp] theorem card_orderedSimplexSource (s t : ℕ) :
    Fintype.card (OrderedSimplexSource s t) = simplexCard s t := by
  classical
  calc
    Fintype.card (OrderedSimplexSource s t) =
        ∑ u : Fin (t - 1), (u.1 + 1) * (s - (u.1 + 1)) := by
      simp [OrderedSimplexSource]
    _ = simplexCard s t := by
      unfold simplexCard
      exact (Fin.sum_univ_eq_sum_range
        (fun u : ℕ => (u + 1) * (s - (u + 1)))) (t - 1)

theorem orderedSimplex_fullCore (S : CyclicStaircase)
    (hord : PairCountsOrdered S)
    (i : OrderedSimplexSource (pair13Count S.D) (pair23Count S.D)) :
    FullCore S (orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) i) := by
  have hsimp := orderedSimplexPoint_mem (pair13Count S.D) (pair23Count S.D) hord.1 i
  have hsr := hord.2
  unfold OrderedSimplex at hsimp
  unfold FullCore
  rcases hsimp with ⟨hx, hy, hz, hyz, hsum⟩
  exact ⟨hx, hy, hz, by omega, by omega, hyz⟩

theorem noFull_orderedSimplex_mem (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (i : OrderedSimplexSource (pair13Count S.D) (pair23Count S.D)) :
    orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) i ∈ S.D :=
  noFull_fullCore_mem S hnf (orderedSimplex_fullCore S hord i)

noncomputable def ThreePlaneSimplexSource (S : CyclicStaircase) :=
  ThreePlaneSource S ⊕
    OrderedSimplexSource (pair13Count S.D) (pair23Count S.D)

noncomputable instance (S : CyclicStaircase) : Fintype (ThreePlaneSimplexSource S) := by
  unfold ThreePlaneSimplexSource
  infer_instance

noncomputable def threePlaneSimplexPoint (S : CyclicStaircase) :
    ThreePlaneSimplexSource S → Point3
  | .inl a => threePlaneSourcePoint S a
  | .inr i => orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) i

theorem threePlaneSimplexPoint_injective (S : CyclicStaircase)
    (hord : PairCountsOrdered S) : Function.Injective (threePlaneSimplexPoint S) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          apply congrArg Sum.inl
          exact threePlaneSourcePoint_injective S h
      | inr b =>
          have hcore := orderedSimplex_fullCore S hord b
          have hfull : FullSupport (orderedSimplexPoint
              (pair13Count S.D) (pair23Count S.D) b) :=
            ⟨hcore.1, hcore.2.1, hcore.2.2.1⟩
          change threePlaneSourcePoint S a = orderedSimplexPoint
            (pair13Count S.D) (pair23Count S.D) b at h
          have : FullSupport (threePlaneSourcePoint S a) := h ▸ hfull
          exact False.elim ((threePlaneSourcePoint_not_fullSupport S a) this)
  | inr a =>
      cases b with
      | inl b =>
          have hcore := orderedSimplex_fullCore S hord a
          have hfull : FullSupport (orderedSimplexPoint
              (pair13Count S.D) (pair23Count S.D) a) :=
            ⟨hcore.1, hcore.2.1, hcore.2.2.1⟩
          change orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) a =
            threePlaneSourcePoint S b at h
          have : FullSupport (threePlaneSourcePoint S b) := h.symm ▸ hfull
          exact False.elim ((threePlaneSourcePoint_not_fullSupport S b) this)
      | inr b =>
          apply congrArg Sum.inr
          exact orderedSimplexPoint_injective _ _ h

theorem threePlane_simplex_card_lower_D (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S) :
    pure1Intercept S + pure2Intercept S + pure3Intercept S - 2
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + simplexCard (pair13Count S.D) (pair23Count S.D) ≤ S.D.card := by
  classical
  let target := {p : Point3 // p ∈ S.D}
  let f : ThreePlaneSimplexSource S → target := fun a =>
    match a with
    | .inl x => ⟨threePlaneSourcePoint S x, threePlaneSourcePoint_mem S x⟩
    | .inr i => ⟨orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) i,
        noFull_orderedSimplex_mem S hnf hord i⟩
  have hf : Function.Injective f := by
    intro a b h
    apply threePlaneSimplexPoint_injective S hord
    have hv := congrArg (fun x : target => x.1) h
    cases a <;> cases b <;> exact hv
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card target = S.D.card := by simp [target]
  have hsource : Fintype.card (ThreePlaneSimplexSource S) =
      Fintype.card (ThreePlaneSource S) +
        simplexCard (pair13Count S.D) (pair23Count S.D) := by
    simp [ThreePlaneSimplexSource]
  rw [hsource, card_threePlaneSource, htarget] at hcard
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

theorem m5_simplex_lower_equal (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + simplexCard (pair13Count S.D) (pair23Count S.D) ≤ S.m := by
  have hcard := threePlane_simplex_card_lower_D S hnf hord
  have hm4 := m4_intercepts_equal S hord heq
  have hD := S.card_D
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

theorem m5_simplex_lower_strict (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + simplexCard (pair13Count S.D) (pair23Count S.D) ≤ S.m := by
  have hcard := threePlane_simplex_card_lower_D S hnf hord
  have hm4 := m4_intercepts_strict S hord hlt
  have hD := S.card_D
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

end NSP3
