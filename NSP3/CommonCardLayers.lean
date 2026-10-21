import NSP3.CommonCardPositive
import NSP3.CommonCardRelativeGraph
import NSP3.RhoPresentation

namespace NSP3.CommonCard

open _root_.CommonCard

def NumericPresentation {A : Type*} [Add A] (w : A → ℕ) (R : Finset (A × A)) : Prop :=
  ∀ u v, GeneratedAddRel R u v ↔ w u = w v

def Homogeneous (g : Fin 4 → ℕ) (R : Finset (FourCoeff × FourCoeff)) : Prop :=
  ∀ e ∈ R, degree g e.1 = degree g e.2

def degreeSlice (g : Fin 4 → ℕ) (n : ℕ) (R : Finset (FourCoeff × FourCoeff)) :
    Finset (FourCoeff × FourCoeff) := R.filter (fun e => degree g e.1 = n)

/-- Intrinsic common-support edges of one numeric fiber. -/
def BaseEdge (g : Fin 4 → ℕ) (n : ℕ) (u v : FourCoeff) : Prop :=
  degree g u = n ∧ degree g v = n ∧ ∃ i, 0 < u i ∧ 0 < v i

theorem generated_replace {A : Type*} [Add A] (R T : Finset (A × A))
    (hs : ∀ e ∈ R, GeneratedAddRel T e.1 e.2) {u v : A}
    (hh : GeneratedAddRel R u v) : GeneratedAddRel T u v := by
  induction hh with
  | edge he => exact hs _ he
  | refl u => exact .refl u
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | context _ d ih => exact .context ih d

theorem generated_mono {A : Type*} [Add A] (R T : Finset (A × A)) (hRT : R ⊆ T)
    {u v : A} (hh : GeneratedAddRel R u v) : GeneratedAddRel T u v :=
  generated_replace R T (fun _ he => .edge (hRT he)) hh

theorem presentation_homogeneous (g : Fin 4 → ℕ) (R : Finset (FourCoeff × FourCoeff))
    (hR : NumericPresentation (degree g) R) : Homogeneous g R :=
  fun e he => (hR e.1 e.2).mp (.edge he)

theorem generated_degree_eq (g : Fin 4 → ℕ) (R : Finset (FourCoeff × FourCoeff))
    (hs : Homogeneous g R) {u v : FourCoeff} (hh : GeneratedAddRel R u v) :
    degree g u = degree g v := by
  induction hh with
  | edge he => exact hs _ he
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | context _ d ih => simp only [degree_add, ih]

/-- An edge of larger degree cannot be used in a derivation of smaller degree. -/
theorem generated_erase_of_lower (g : Fin 4 → ℕ) (R : Finset (FourCoeff × FourCoeff))
    (hs : Homogeneous g R) (e : FourCoeff × FourCoeff) {u v : FourCoeff}
    (hh : GeneratedAddRel R u v) :
    degree g u < degree g e.1 → GeneratedAddRel (R.erase e) u v := by
  classical
  induction hh with
  | edge hf =>
    intro hl
    apply GeneratedAddRel.edge
    refine Finset.mem_erase.mpr ⟨?_, hf⟩
    intro he
    cases he
    simp only [Prod.fst] at hl
    exact Nat.lt_irrefl _ hl
  | refl u => intro _; exact .refl u
  | symm hh ih =>
    intro hl
    apply GeneratedAddRel.symm
    exact ih (by rw [generated_degree_eq g R hs hh]; exact hl)
  | trans hh₁ hh₂ ih₁ ih₂ =>
    intro hl
    exact .trans (ih₁ hl) (ih₂ (by rw [← generated_degree_eq g R hs hh₁]; exact hl))
  | context hh d ih =>
    intro hl
    apply GeneratedAddRel.context
    apply ih
    rw [degree_add] at hl
    omega

theorem minimal_edge_not_generated {A : Type*} [Add A] [DecidableEq A]
    (w : A → ℕ) (R : Finset (A × A)) (hR : NumericPresentation w R)
    (hmin : ∀ T, T ⊂ R → ¬ NumericPresentation w T) (e : A × A) (he : e ∈ R) :
    ¬ GeneratedAddRel (R.erase e) e.1 e.2 := by
  intro hh
  apply hmin (R.erase e) (Finset.erase_ssubset he)
  intro u v
  constructor
  · intro h
    exact (hR u v).mp (generated_mono _ _ (Finset.erase_subset _ _) h)
  · intro hw
    apply generated_replace R (R.erase e) ?_ ((hR u v).mpr hw)
    intro f hf
    by_cases hfe : f=e
    · subst f; exact hh
    · exact .edge (Finset.mem_erase.mpr ⟨hfe,hf⟩)

/-- Every homogeneous derivation projects to support connectivity plus same-degree edges. -/
theorem generated_joined_slice (g : Fin 4 → ℕ) (R : Finset (FourCoeff × FourCoeff))
    (hs : Homogeneous g R) {u v : FourCoeff} (hh : GeneratedAddRel R u v) :
    ∀ n, degree g u = n → joined (BaseEdge g n) (degreeSlice g n R) u v := by
  classical
  induction hh with
  | edge he =>
    intro n hn
    exact .rel _ _ (Or.inr (Finset.mem_filter.mpr ⟨he,hn⟩))
  | refl u => intro _ _; exact .refl u
  | symm hh ih =>
    intro n hn
    exact .symm _ _ (ih n ((generated_degree_eq g R hs hh).trans hn))
  | trans hh₁ hh₂ ih₁ ih₂ =>
    intro n hn
    exact .trans _ _ _ (ih₁ n hn)
      (ih₂ n ((generated_degree_eq g R hs hh₁).symm.trans hn))
  | context hh d ih =>
    intro n hn
    by_cases hd : d=0
    · subst d
      simpa only [add_zero] using ih n (by simpa only [add_zero] using hn)
    · apply Relation.EqvGen.rel
      apply Or.inl
      refine ⟨hn, ?_, context_common_support _ _ d hd⟩
      rw [degree_add, ← generated_degree_eq g R hs hh, ← degree_add]
      exact hn

theorem joined_to_generated (g : Fin 4 → ℕ) (n : ℕ)
    (P Q : Finset (FourCoeff × FourCoeff))
    (hb : ∀ u v, BaseEdge g n u v → GeneratedAddRel Q u v)
    (hp : ∀ e ∈ P, GeneratedAddRel Q e.1 e.2) {u v : FourCoeff}
    (hh : joined (BaseEdge g n) P u v) : GeneratedAddRel Q u v := by
  induction hh with
  | rel u v he =>
    rcases he with he | he
    · exact hb u v he
    · exact hp _ he
  | refl u => exact .refl u
  | symm _ _ _ ih => exact .symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Base support connectivity in degree n survives deletion of an edge of degree n. -/
theorem baseEdge_erase_generated (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (R : Finset (FourCoeff × FourCoeff)) (hR : NumericPresentation (degree g) R)
    (n : ℕ) (e : FourCoeff × FourCoeff) (he : degree g e.1 = n)
    {u v : FourCoeff} (hb : BaseEdge g n u v) : GeneratedAddRel (R.erase e) u v := by
  obtain ⟨i,u',v',hu,hv,heq,hl⟩ :=
    support_edge_strict_lower g hg u v (hb.1.trans hb.2.1.symm) hb.2.2
  have hh := (hR u' v').mpr heq
  have hun := hb.1
  have hh' := generated_erase_of_lower g R (presentation_homogeneous g R hR) e hh
    (by omega)
  rw [hu,hv]
  exact .context hh' (Pi.single i 1)

theorem degreeSlice_indispensable (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (R : Finset (FourCoeff × FourCoeff)) (hR : NumericPresentation (degree g) R)
    (hmin : ∀ T, T ⊂ R → ¬ NumericPresentation (degree g) T) (n : ℕ) :
    ∀ e ∈ degreeSlice g n R, ¬ joined (BaseEdge g n) ((degreeSlice g n R).erase e) e.1 e.2 := by
  classical
  intro e he hh
  obtain ⟨heR,hen⟩ := Finset.mem_filter.mp he
  apply minimal_edge_not_generated (degree g) R hR hmin e heR
  apply joined_to_generated g n ((degreeSlice g n R).erase e) (R.erase e) ?_ ?_ hh
  · intro u v hb
    exact baseEdge_erase_generated g hg R hR n e hen hb
  · intro f hf
    obtain ⟨hne,hf⟩ := Finset.mem_erase.mp hf
    exact .edge (Finset.mem_erase.mpr ⟨hne,(Finset.mem_filter.mp hf).1⟩)

theorem minimal_degree_card_eq (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (R T : Finset (FourCoeff × FourCoeff))
    (hR : NumericPresentation (degree g) R) (hT : NumericPresentation (degree g) T)
    (iR : ∀ P, P ⊂ R → ¬ NumericPresentation (degree g) P)
    (iT : ∀ P, P ⊂ T → ¬ NumericPresentation (degree g) P) (n : ℕ) :
    (degreeSlice g n R).card = (degreeSlice g n T).card := by
  classical
  apply _root_.CommonCard.relative_card_eq_of_mutual (BaseEdge g n)
  · intro e he
    obtain ⟨heT,hen⟩ := Finset.mem_filter.mp he
    exact generated_joined_slice g R (presentation_homogeneous g R hR)
      ((hR e.1 e.2).mpr (presentation_homogeneous g T hT e heT)) n hen
  · intro e he
    obtain ⟨heR,hen⟩ := Finset.mem_filter.mp he
    exact generated_joined_slice g T (presentation_homogeneous g T hT)
      ((hT e.1 e.2).mpr (presentation_homogeneous g R hR e heR)) n hen
  · exact degreeSlice_indispensable g hg R hR iR n
  · exact degreeSlice_indispensable g hg T hT iT n

theorem minimal_numeric_card_eq (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (R T : Finset (FourCoeff × FourCoeff))
    (hR : NumericPresentation (degree g) R) (hT : NumericPresentation (degree g) T)
    (iR : ∀ P, P ⊂ R → ¬ NumericPresentation (degree g) P)
    (iT : ∀ P, P ⊂ T → ¬ NumericPresentation (degree g) P) : R.card = T.card := by
  classical
  let D := (R ∪ T).image (fun e => degree g e.1)
  have hr : R.card = ∑ n ∈ D, (degreeSlice g n R).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro e he
    exact Finset.mem_image_of_mem _ (Finset.mem_union_left T he)
  have ht : T.card = ∑ n ∈ D, (degreeSlice g n T).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro e he
    exact Finset.mem_image_of_mem _ (Finset.mem_union_right R he)
  rw [hr,ht]
  exact Finset.sum_congr rfl (fun n _ => minimal_degree_card_eq g hg R T hR hT iR iT n)

end NSP3.CommonCard
