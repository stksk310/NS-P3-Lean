import NSP3.CertifiedRowVerifier

namespace NSP3

/-- Nodes are stored parent-first: children can only be nodes in the strict tail.
The stored missing residue is a hint, not an externally trusted assertion. -/
structure CoverDAGNode where
  points : Finset Point3
  missing : ℕ

def coverDAGNodeCheck {m : ℕ} [NeZero m] (q : FullResidualTuple) (g : Point3)
    (w : ResidueWeights m) (U : Finset Point3)
    (prior : List CoverDAGNode) (node : CoverDAGNode) : Bool :=
  decide (m < node.points.card ∨
    (node.points.card = m ∧ ¬ terminalMatches q m g node.points) ∨
    ((node.missing : ZMod m) ∉ node.points.image (residueWithWeights w) ∧
      ∀ p ∈ U, residueWithWeights w p = (node.missing : ZMod m) →
        residueInjectiveOn (node.points ∪ fastSeedLowerBox p) w → ¬ g ≤ p →
        ∃ child ∈ prior, child.points = node.points ∪ fastSeedLowerBox p))

def coverDAGCheck {m : ℕ} [NeZero m] (q : FullResidualTuple) (g : Point3)
    (w : ResidueWeights m) (U : Finset Point3) : List CoverDAGNode → Bool
  | [] => true
  | node :: prior => coverDAGNodeCheck q g w U prior node && coverDAGCheck q g w U prior

/-- Every candidate branch is checked against the complete U. Tail membership
prevents circular justification; an omitted compatible child cannot certify. -/
theorem coverDAGCheck_sound {m : ℕ} [NeZero m] (q : FullResidualTuple)
    (g : Point3) (w : ResidueWeights m) (U : Finset Point3)
    (nodes : List CoverDAGNode) (hv : coverDAGCheck q g w U nodes = true)
    (node : CoverDAGNode) (hn : node ∈ nodes) (D : Finset Point3)
    (hd : IsDownset D) (hs : node.points ⊆ D) (hu : D ⊆ U)
    (hi : residueInjectiveOn D w) (hc : D.card = m) (hg : g ∉ D) :
    ¬ terminalMatches q m g D := by
  induction nodes generalizing node with
  | nil => exact False.elim (List.not_mem_nil hn)
  | cons root prior ih =>
      have hv' := Bool.and_eq_true_iff.mp hv
      rcases List.mem_cons.mp hn with he | hn
      · subst node
        have hlocal := of_decide_eq_true hv'.1
        rcases hlocal with hlarge | ⟨heq,hnot⟩ | ⟨hmissing,hbranches⟩
        · have hle := Finset.card_le_card hs
          omega
        · have hAD : root.points = D := Finset.eq_of_subset_of_card_le hs (by omega)
          simpa [hAD] using hnot
        · have hrD : (root.missing : ZMod m) ∈ D.image (residueWithWeights w) := by
            rw [residue_image_eq_univ w D hi hc]
            exact Finset.mem_univ _
          obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hrD
          have hsub : root.points ∪ fastSeedLowerBox p ⊆ D := by
            intro a ha
            rcases Finset.mem_union.mp ha with ha | ha
            · exact hs ha
            · rw [fastSeedLowerBox_eq,mem_seedLowerBox] at ha
              exact hd.mem_of_le ha hp
          obtain ⟨child,hchild,hA⟩ := hbranches p (hu hp) he
            (residueInjectiveOn_mono w hsub hi) (fun h => hg (hd.mem_of_le h hp))
          exact ih hv'.2 child hchild (hA ▸ hsub)
      · exact ih hv'.2 node hn hs

def certificateRowDAGCheck (row : CertificateRow) (nodes : List CoverDAGNode) : Bool :=
  if hm : row.m = 0 then false else
    letI : NeZero row.m := ⟨hm⟩
    let A := fastMandatorySeed row.q row.g
    let w := certificateRowWeights row
    decide (residueInjectiveOn A w ∧ ∃ root ∈ nodes, root.points = A) &&
      coverDAGCheck row.q row.g w (compactCoverPoints w A row.g) nodes

/-- Exact completion semantics, with U derived and proved complete, not supplied
as an unverified generator restriction. -/
theorem certificateRowDAGCheck_sound (row : CertificateRow) [NeZero row.m]
    (nodes : List CoverDAGNode) (hv : certificateRowDAGCheck row nodes = true)
    (D : Finset Point3) (hD : D ∈ downsetCompletions
      (row.m - (mandatorySeed row.q row.g).card) row.m
      (certificateRowWeights row) (mandatorySeed row.q row.g)) :
    ¬ terminalMatches row.q row.m row.g D := by
  simp only [certificateRowDAGCheck,dite_eq_right (NeZero.ne row.m)] at hv
  have hv' := Bool.and_eq_true_iff.mp hv
  obtain ⟨hi,root,hroot,hA⟩ := of_decide_eq_true hv'.1
  rw [fastMandatorySeed_eq] at hi hA hv'
  intro ht
  obtain ⟨hs,hd,hinj,_⟩ := completion_cover_invariants _ row.m
    (certificateRowWeights row) (pointBox row.m ∪ mandatorySeed row.q row.g)
    (mandatorySeed row.q row.g) D (mandatorySeed_isDownset _ _) hi
    Finset.subset_union_right Finset.subset_union_left hD
  have hu := downset_subset_compactCoverPoints _ _ _ _ hd hs hinj ht.1 ht.2.1.not_mem
  exact coverDAGCheck_sound row.q row.g (certificateRowWeights row) _ nodes hv'.2
    root hroot D hd (hA ▸ hs) hu hinj ht.1 ht.2.1.not_mem ht

end NSP3
