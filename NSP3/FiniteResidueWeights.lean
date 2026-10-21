import NSP3.MandatorySeed

namespace NSP3

/-- An unquotiented triple of cyclic weights.  Enumerating this entire finite
type avoids every unit-normalization and gcd-lift side condition. -/
structure ResidueWeights (m : ℕ) where
  p1 : ZMod m
  p2 : ZMod m
  p3 : ZMod m
deriving DecidableEq, Repr

def residueWithWeights {m : ℕ} (w : ResidueWeights m) (p : Point3) : ZMod m :=
  residueOf w.p1 w.p2 w.p3 p

private def residueWeightsEmbedding (m : ℕ) :
    (ZMod m × (ZMod m × ZMod m)) ↪ ResidueWeights m where
  toFun a := ⟨a.1, a.2.1, a.2.2⟩
  inj' := by
    intro a b h
    rcases a with ⟨a1, a2, a3⟩
    rcases b with ⟨b1, b2, b3⟩
    simp only [Prod.mk.injEq]
    exact ⟨congrArg ResidueWeights.p1 h,
      ⟨congrArg ResidueWeights.p2 h, congrArg ResidueWeights.p3 h⟩⟩

/-- Complete, deliberately unquotiented enumeration of all weight triples. -/
def allResidueWeights (m : ℕ) [NeZero m] : Finset (ResidueWeights m) :=
  ((Finset.univ : Finset (ZMod m)).product
    ((Finset.univ : Finset (ZMod m)).product (Finset.univ : Finset (ZMod m)))).map
      (residueWeightsEmbedding m)

@[simp] theorem mem_allResidueWeights (m : ℕ) [NeZero m]
    (w : ResidueWeights m) : w ∈ allResidueWeights m := by
  apply Finset.mem_map.mpr
  exact ⟨(w.p1, (w.p2, w.p3)), by simp, by cases w; rfl⟩

/-- Weight triples for which the distinguished boundary has residue zero. -/
def boundaryResidueWeights (m : ℕ) [NeZero m] (g : Point3) :
    Finset (ResidueWeights m) :=
  (allResidueWeights m).filter fun w => residueWithWeights w g = 0

@[simp] theorem mem_boundaryResidueWeights (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) :
    w ∈ boundaryResidueWeights m g ↔ residueWithWeights w g = 0 := by
  simp [boundaryResidueWeights]

def actualResidueWeights (S : CyclicStaircase) : ResidueWeights S.m where
  p1 := S.p1
  p2 := S.p2
  p3 := S.p3

@[simp] theorem residueWithWeights_actual (S : CyclicStaircase) (p : Point3) :
    residueWithWeights (actualResidueWeights S) p = S.residue p := rfl

/-- The full boundary equation used by the finite filter. -/
theorem fullSupport_residue_eq_zero (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    S.residue g = 0 := by
  rw [← S.residue_rho g, fullSupport_return_eq_zero S hg hfull,
    S.residue_zero]

/-- Completeness of the unquotiented weight enumeration for an actual state. -/
theorem actualResidueWeights_mem_boundary (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
    actualResidueWeights S ∈ boundaryResidueWeights S.m g := by
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  rw [mem_boundaryResidueWeights, residueWithWeights_actual]
  exact fullSupport_residue_eq_zero S hg hfull

/-- Decidable finite formulation of injectivity on a candidate seed. -/
def residueInjectiveOn {m : ℕ} (D : Finset Point3) (w : ResidueWeights m) : Prop :=
  (D.image (residueWithWeights w)).card = D.card

instance {m : ℕ} (D : Finset Point3) (w : ResidueWeights m) :
    Decidable (residueInjectiveOn D w) := by
  unfold residueInjectiveOn
  infer_instance

theorem actualResidueWeights_injective_on_standardSet (S : CyclicStaircase) :
    residueInjectiveOn S.D (actualResidueWeights S) := by
  rw [residueInjectiveOn, Finset.card_image_iff]
  intro a ha b hb hab
  apply S.standard_eq_of_residue_eq ha hb
  simpa only [residueWithWeights_actual] using hab

/-- The actual weights are injective on the complete mandatory seed, not just
on its separately generated components. -/
theorem actualResidueWeights_injective_on_mandatorySeed
    (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    residueInjectiveOn
      (mandatorySeed
        (FullResidualTuple.mk (pair12Count S.D) (pair13Count S.D)
          (pair23Count S.D)) g)
      (actualResidueWeights S) := by
  rw [residueInjectiveOn, Finset.card_image_iff]
  intro a ha b hb hab
  apply S.standard_eq_of_residue_eq
  · exact mandatorySeed_subset_standardSet S hg hfull ha
  · exact mandatorySeed_subset_standardSet S hg hfull hb
  · simpa only [residueWithWeights_actual] using hab

end NSP3
