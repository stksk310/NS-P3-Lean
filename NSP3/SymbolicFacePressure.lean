import NSP3.PureIntercepts
import NSP3.PairBoundaryCounts

namespace NSP3

/-- A corner partition above a standard face. No residue assumption is used here. -/
theorem ferrers_face_axis_pressure {B : Finset Point3} {u v : Point3 → ℕ}
    {A C U V : ℕ} (hA : A ≤ U) (hC : C ≤ V)
    (hu : ∀ b ∈ B, u b ≤ U) (hv : ∀ b ∈ B, v b ≤ V)
    (huinj : Set.InjOn u (B : Set Point3))
    (hvinj : Set.InjOn v (B : Set Point3))
    (hface : ∀ b ∈ B, u b ≤ A → C < v b) : B.card+A+C ≤ U+V := by
  classical
  let l := B.filter fun b => A < u b
  let r := B.filter fun b => ¬ A < u b
  have hlmaps : Set.MapsTo u (l : Set Point3) (Finset.Ioc A U : Set ℕ) := by
    intro b hb
    obtain ⟨hb, hgt⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_Ioc.mpr ⟨hgt, hu b hb⟩
  have hlinj : Set.InjOn u (l : Set Point3) := by
    intro b hb c hc heq
    exact huinj (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hc).1 heq
  have hrmaps : Set.MapsTo v (r : Set Point3) (Finset.Ioc C V : Set ℕ) := by
    intro b hb
    obtain ⟨hb, hnot⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_Ioc.mpr ⟨hface b hb (by omega), hv b hb⟩
  have hrinj : Set.InjOn v (r : Set Point3) := by
    intro b hb c hc heq
    exact hvinj (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hc).1 heq
  have hlcard := Finset.card_le_card_of_injOn u hlmaps hlinj
  have hrcard := Finset.card_le_card_of_injOn v hrmaps hrinj
  have hpart : l.card+r.card=B.card :=
    Finset.card_filter_add_card_filter_not (s := B) (fun b => A < u b)
  simp only [Nat.card_Ioc] at hlcard hrcard
  omega

theorem pair12_face_axis_pressure (S : CyclicStaircase) {A B : ℕ}
    (hm : Point3.mk A B 0 ∈ S.D) :
    pair12Count S.D+A+B ≤ (pure1Intercept S-1)+(pure2Intercept S-1) := by
  have hA : A ≤ pure1Intercept S-1 := by
    have ha := S.down_closed (show Point3.mk A 0 0 ≤ Point3.mk A B 0 from
      ⟨le_rfl, Nat.zero_le _, le_rfl⟩) hm
    have := (pure1_axis_mem_iff S A).mp ha
    omega
  have hB : B ≤ pure2Intercept S-1 := by
    have hb := S.down_closed (show Point3.mk 0 B 0 ≤ Point3.mk A B 0 from
      ⟨Nat.zero_le _, le_rfl, le_rfl⟩) hm
    have := (pure2_axis_mem_iff S B).mp hb
    omega
  apply ferrers_face_axis_pressure (u := Point3.x) (v := Point3.y) hA hB
  · intro b hb
    obtain ⟨hbmin, hp⟩ := mem_pair12Boundaries.mp hb
    have haxis : Point3.mk b.x 0 0 ∈ S.D := S.down_closed (b := b.pred2)
      ⟨le_rfl, Nat.zero_le _, Nat.zero_le _⟩ (hbmin.pred2_mem hp.2.1)
    have := (pure1_axis_mem_iff S _).mp haxis
    omega
  · intro b hb
    obtain ⟨hbmin, hp⟩ := mem_pair12Boundaries.mp hb
    have haxis : Point3.mk 0 b.y 0 ∈ S.D := S.down_closed (b := b.pred1)
      ⟨Nat.zero_le _, le_rfl, Nat.zero_le _⟩ (hbmin.pred1_mem hp.1)
    have := (pure2_axis_mem_iff S _).mp haxis
    omega
  · intro b hb c hc heq
    exact pair12_eq_of_x_eq S.down_closed hb hc heq
  · intro b hb c hc heq
    exact pair12_eq_of_y_eq S.down_closed hb hc heq
  · intro b hb hbx
    obtain ⟨hbmin, hp⟩ := mem_pair12Boundaries.mp hb
    by_contra hnot
    have hby : b.y ≤ B := by omega
    exact hbmin.not_mem (S.down_closed (b := Point3.mk A B 0)
      ⟨hbx, hby, by simp [hp.2.2]⟩ hm)

theorem pair13_face_axis_pressure (S : CyclicStaircase) {A B : ℕ}
    (hm : Point3.mk A 0 B ∈ S.D) :
    pair13Count S.D+A+B ≤ (pure1Intercept S-1)+(pure3Intercept S-1) := by
  have hA : A ≤ pure1Intercept S-1 := by
    have ha := S.down_closed (show Point3.mk A 0 0 ≤ Point3.mk A 0 B from
      ⟨le_rfl, le_rfl, Nat.zero_le _⟩) hm
    have := (pure1_axis_mem_iff S A).mp ha
    omega
  have hB : B ≤ pure3Intercept S-1 := by
    have hb := S.down_closed (show Point3.mk 0 0 B ≤ Point3.mk A 0 B from
      ⟨Nat.zero_le _, le_rfl, le_rfl⟩) hm
    have := (pure3_axis_mem_iff S B).mp hb
    omega
  apply ferrers_face_axis_pressure (u := Point3.x) (v := Point3.z) hA hB
  · intro b hb
    obtain ⟨hbmin, hp⟩ := mem_pair13Boundaries.mp hb
    have haxis : Point3.mk b.x 0 0 ∈ S.D := S.down_closed (b := b.pred3)
      ⟨le_rfl, Nat.zero_le _, Nat.zero_le _⟩ (hbmin.pred3_mem hp.2.2)
    have := (pure1_axis_mem_iff S _).mp haxis
    omega
  · intro b hb
    obtain ⟨hbmin, hp⟩ := mem_pair13Boundaries.mp hb
    have haxis : Point3.mk 0 0 b.z ∈ S.D := S.down_closed (b := b.pred1)
      ⟨Nat.zero_le _, Nat.zero_le _, le_rfl⟩ (hbmin.pred1_mem hp.1)
    have := (pure3_axis_mem_iff S _).mp haxis
    omega
  · intro b hb c hc heq
    exact pair13_eq_of_x_eq S.down_closed hb hc heq
  · intro b hb c hc heq
    exact pair13_eq_of_z_eq S.down_closed hb hc heq
  · intro b hb hbx
    obtain ⟨hbmin, hp⟩ := mem_pair13Boundaries.mp hb
    by_contra hnot
    have hbz : b.z ≤ B := by omega
    exact hbmin.not_mem (S.down_closed (b := Point3.mk A 0 B)
      ⟨hbx, by simp [hp.2.1], hbz⟩ hm)

theorem pair23_face_axis_pressure (S : CyclicStaircase) {A B : ℕ}
    (hm : Point3.mk 0 A B ∈ S.D) :
    pair23Count S.D+A+B ≤ (pure2Intercept S-1)+(pure3Intercept S-1) := by
  have hA : A ≤ pure2Intercept S-1 := by
    have ha := S.down_closed (show Point3.mk 0 A 0 ≤ Point3.mk 0 A B from
      ⟨le_rfl, le_rfl, Nat.zero_le _⟩) hm
    have := (pure2_axis_mem_iff S A).mp ha
    omega
  have hB : B ≤ pure3Intercept S-1 := by
    have hb := S.down_closed (show Point3.mk 0 0 B ≤ Point3.mk 0 A B from
      ⟨le_rfl, Nat.zero_le _, le_rfl⟩) hm
    have := (pure3_axis_mem_iff S B).mp hb
    omega
  apply ferrers_face_axis_pressure (u := Point3.y) (v := Point3.z) hA hB
  · intro b hb
    obtain ⟨hbmin, hp⟩ := mem_pair23Boundaries.mp hb
    have haxis : Point3.mk 0 b.y 0 ∈ S.D := S.down_closed (b := b.pred3)
      ⟨Nat.zero_le _, le_rfl, Nat.zero_le _⟩ (hbmin.pred3_mem hp.2.2)
    have := (pure2_axis_mem_iff S _).mp haxis
    omega
  · intro b hb
    obtain ⟨hbmin, hp⟩ := mem_pair23Boundaries.mp hb
    have haxis : Point3.mk 0 0 b.z ∈ S.D := S.down_closed (b := b.pred2)
      ⟨Nat.zero_le _, Nat.zero_le _, le_rfl⟩ (hbmin.pred2_mem hp.2.1)
    have := (pure3_axis_mem_iff S _).mp haxis
    omega
  · intro b hb c hc heq
    exact pair23_eq_of_y_eq S.down_closed hb hc heq
  · intro b hb c hc heq
    exact pair23_eq_of_z_eq S.down_closed hb hc heq
  · intro b hb hby
    obtain ⟨hbmin, hp⟩ := mem_pair23Boundaries.mp hb
    by_contra hnot
    have hbz : b.z ≤ B := by omega
    exact hbmin.not_mem (S.down_closed (b := Point3.mk 0 A B)
      ⟨by simp [hp.1], hby, hbz⟩ hm)

end NSP3
