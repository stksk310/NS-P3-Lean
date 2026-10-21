import NSP3.PlaneResources

namespace NSP3

noncomputable def balancedAxisExcess1 (S : CyclicStaircase) : ℕ :=
  pure1Intercept S - (pair12Count S.D + 1)

noncomputable def balancedAxisExcess2 (S : CyclicStaircase) : ℕ :=
  pure2Intercept S - (pair12Count S.D + 1)

noncomputable def balancedAxisExcess3 (S : CyclicStaircase) : ℕ :=
  pure3Intercept S - (pair12Count S.D + 1)

noncomputable def balancedResourceExcess (S : CyclicStaircase) : ℕ :=
  balancedAxisExcess1 S + balancedAxisExcess2 S + balancedAxisExcess3 S
    + (pair12ExtraFinset S).card + (pair13ExtraFinset S).card
    + (pair23ExtraFinset S).card

theorem balanced_axis1_baseline (S : CyclicStaircase) :
    pair12Count S.D + 1 ≤ pure1Intercept S := pair12_intercept1_lower S

theorem balanced_axis2_baseline (S : CyclicStaircase) :
    pair12Count S.D + 1 ≤ pure2Intercept S := pair12_intercept2_lower S

theorem balanced_axis3_baseline (S : CyclicStaircase)
    (heq : pair12Count S.D = pair13Count S.D) :
    pair12Count S.D + 1 ≤ pure3Intercept S := by
  have h := pair13_intercept3_lower S
  omega

private def BalancedResourceSource (S : CyclicStaircase) :=
  Unit ⊕ (Fin (pure1Intercept S - 1) ⊕
    (Fin (pure2Intercept S - 1) ⊕
      (Fin (pure3Intercept S - 1) ⊕
        ({p : Point3 // p ∈ plane12PosFinset S} ⊕
          ({p : Point3 // p ∈ plane13PosFinset S} ⊕
            ({p : Point3 // p ∈ plane23PosFinset S} ⊕
              {p : Point3 // p ∈ fullCoreFinset S}))))))

private noncomputable instance (S : CyclicStaircase) :
    Fintype (BalancedResourceSource S) := by
  unfold BalancedResourceSource
  let _ : Fintype {p : Point3 // p ∈ plane12PosFinset S} := Fintype.ofFinite _
  let _ : Fintype {p : Point3 // p ∈ plane13PosFinset S} := Fintype.ofFinite _
  let _ : Fintype {p : Point3 // p ∈ plane23PosFinset S} := Fintype.ofFinite _
  let _ : Fintype {p : Point3 // p ∈ fullCoreFinset S} := Fintype.ofFinite _
  infer_instance

private def balancedResourcePoint (S : CyclicStaircase) :
    BalancedResourceSource S → Point3
  | .inl _ => ⟨0, 0, 0⟩
  | .inr (.inl i) => ⟨i.1 + 1, 0, 0⟩
  | .inr (.inr (.inl i)) => ⟨0, i.1 + 1, 0⟩
  | .inr (.inr (.inr (.inl i))) => ⟨0, 0, i.1 + 1⟩
  | .inr (.inr (.inr (.inr (.inl p)))) => p.1
  | .inr (.inr (.inr (.inr (.inr (.inl p))))) => p.1
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl p)))))) => p.1
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr p)))))) => p.1

private def balancedResourcePointTag (p : Point3) : ℕ :=
  if p.x = 0 then
    if p.y = 0 then if p.z = 0 then 0 else 3
    else if p.z = 0 then 2 else 6
  else if p.y = 0 then
    if p.z = 0 then 1 else 5
  else if p.z = 0 then 4 else 7

private def balancedResourceSourceTag (S : CyclicStaircase) :
    BalancedResourceSource S → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr (.inl _))) => 3
  | .inr (.inr (.inr (.inr (.inl _)))) => 4
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => 5
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))) => 6
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))) => 7

private theorem balancedResourcePointTag_source (S : CyclicStaircase)
    (s : BalancedResourceSource S) :
    balancedResourcePointTag (balancedResourcePoint S s) =
      balancedResourceSourceTag S s := by
  rcases s with u | i | j | k | p12 | p13 | p23 | pfull
  · simp [balancedResourcePointTag, balancedResourcePoint, balancedResourceSourceTag]
  · simp [balancedResourcePointTag, balancedResourcePoint, balancedResourceSourceTag]
  · simp [balancedResourcePointTag, balancedResourcePoint, balancedResourceSourceTag]
  · simp [balancedResourcePointTag, balancedResourcePoint, balancedResourceSourceTag]
  · have hp := (mem_plane12PosFinset S p12.1).mp p12.2
    simp [balancedResourcePointTag, balancedResourcePoint, balancedResourceSourceTag,
      hp.2.1.ne', hp.2.2.1.ne', hp.2.2.2]
  · have hp := (mem_plane13PosFinset S p13.1).mp p13.2
    simp [balancedResourcePointTag, balancedResourcePoint, balancedResourceSourceTag,
      hp.2.1.ne', hp.2.2.1, hp.2.2.2.ne']
  · have hp := (mem_plane23PosFinset S p23.1).mp p23.2
    simp [balancedResourcePointTag, balancedResourcePoint, balancedResourceSourceTag,
      hp.2.1, hp.2.2.1.ne', hp.2.2.2.ne']
  · have hp := (mem_fullCoreFinset S pfull.1).mp pfull.2
    simp [balancedResourcePointTag, balancedResourcePoint, balancedResourceSourceTag,
      hp.1.ne', hp.2.1.ne', hp.2.2.1.ne']

private theorem balancedResourcePoint_injective (S : CyclicStaircase) :
    Function.Injective (balancedResourcePoint S) := by
  intro s t h
  have htag : balancedResourceSourceTag S s = balancedResourceSourceTag S t := by
    rw [← balancedResourcePointTag_source S s, ← balancedResourcePointTag_source S t, h]
  rcases s with u | i | j | k | p12 | p13 | p23 | pfull <;>
    rcases t with v | i' | j' | k' | r12 | r13 | r23 | rfull <;>
    simp [balancedResourceSourceTag] at htag
  · cases u; cases v; rfl
  · apply congrArg (fun x => Sum.inr (Sum.inl x))
    apply Fin.ext
    simpa [balancedResourcePoint] using congrArg Point3.x h
  · apply congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x)))
    apply Fin.ext
    simpa [balancedResourcePoint] using congrArg Point3.y h
  · apply congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inl x))))
    apply Fin.ext
    simpa [balancedResourcePoint] using congrArg Point3.z h
  · congr 4
    apply congrArg Sum.inl
    exact Subtype.ext h
  · congr 5
    apply congrArg Sum.inl
    exact Subtype.ext h
  · congr 6
    apply congrArg Sum.inl
    exact Subtype.ext h
  · congr 7
    exact Subtype.ext h

private theorem balancedResourcePoint_mem (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (s : BalancedResourceSource S) :
    balancedResourcePoint S s ∈ S.D := by
  rcases s with u | i | j | k | p12 | p13 | p23 | pfull
  · simpa [balancedResourcePoint, Point3.zero] using S.zero_mem
  · apply (pure1_axis_mem_iff S (i.1 + 1)).mpr
    omega
  · apply (pure2_axis_mem_iff S (j.1 + 1)).mpr
    omega
  · apply (pure3_axis_mem_iff S (k.1 + 1)).mpr
    omega
  · exact (mem_plane12PosFinset S p12.1).mp p12.2 |>.1
  · exact (mem_plane13PosFinset S p13.1).mp p13.2 |>.1
  · exact (mem_plane23PosFinset S p23.1).mp p23.2 |>.1
  · exact fullCoreFinset_subset_D S hnf pfull.2

theorem actualResource_card_lower (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) :
    1 + (pure1Intercept S - 1) + (pure2Intercept S - 1)
        + (pure3Intercept S - 1)
        + (plane12PosFinset S).card + (plane13PosFinset S).card
        + (plane23PosFinset S).card + (fullCoreFinset S).card ≤ S.m := by
  classical
  let target := {p : Point3 // p ∈ S.D}
  let f : BalancedResourceSource S → target :=
    fun s => ⟨balancedResourcePoint S s, balancedResourcePoint_mem S hnf s⟩
  have hf : Function.Injective f := by
    intro a b h
    apply balancedResourcePoint_injective S
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card target = S.D.card := by simp [target]
  have hsource : Fintype.card (BalancedResourceSource S) =
      1 + (pure1Intercept S - 1) + (pure2Intercept S - 1)
        + (pure3Intercept S - 1)
        + (plane12PosFinset S).card + (plane13PosFinset S).card
        + (plane23PosFinset S).card + (fullCoreFinset S).card := by
    simp [BalancedResourceSource, Nat.add_assoc]
  rw [hsource, htarget] at hcard
  simpa [S.card_D] using hcard

theorem balanced_resource_accounting (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (_hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card
        + balancedResourceExcess S ≤ S.m := by
  have hcard := actualResource_card_lower S hnf
  rw [card_plane12PosFinset, card_plane13PosFinset, card_plane23PosFinset] at hcard
  have h1 := balanced_axis1_baseline S
  have h2 := balanced_axis2_baseline S
  have h3 := balanced_axis3_baseline S heq
  unfold balancedResourceExcess balancedAxisExcess1 balancedAxisExcess2 balancedAxisExcess3
  have hp1 := (pure1Intercept_pure S).1
  have hp2 := (pure2Intercept_pure S).2.1
  have hp3 := (pure3Intercept_pure S).2.2
  omega

end NSP3
