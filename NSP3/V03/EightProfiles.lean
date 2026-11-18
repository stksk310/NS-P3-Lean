import NSP3.SymbolicBWExceptional

/-!
V03's common eight-profile endpoint proof.  The actual H is transported to
its proved exact row formula.  A kernel-decided finite table handles the
complement of the independently proved unbounded-coordinate branch.
No old endpoint sharp theorem is used.
-/
namespace NSP3.V03
open Finset

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The eight profiles left by the wide-strip estimates, in manuscript order. -/
def endpointProfile (i : Fin 8) : Point3 :=
  ![⟨4,4,4⟩,⟨5,4,4⟩,⟨6,4,4⟩,⟨7,4,4⟩,
    ⟨5,5,4⟩,⟨6,5,4⟩,⟨6,6,4⟩,⟨5,5,5⟩] i

def endpointK (i : Fin 8) : ℕ := ![18,19,18,18,22,23,26,27] i
def endpointGap (i : Fin 8) : ℕ := ![0,3,6,9,2,5,4,5] i
def endpointDomainCard (i : Fin 8) : ℕ := ![206,196,181,160,196,181,181,196] i
def endpointWitness (i : Fin 8) : Point3 :=
  ![⟨1,1,4⟩,⟨1,5,1⟩,⟨3,4,1⟩,⟨4,4,1⟩,
    ⟨5,1,1⟩,⟨5,2,1⟩,⟨6,1,1⟩,⟨1,1,5⟩] i

def endpointTarget (r s t : ℕ) : ℕ := quarterSquareCeil (r+s+t+2)
def endpointBaseline (r s t : ℕ) : ℕ :=
  1+3*r+Nat.choose r 2+Nat.choose s 2+Nat.choose t 2

/-- The exact H row, already geometrically proved in symbolic_H_row_card. -/
def endpointHRow (r s t A B C y z : ℕ) : ℕ :=
  let L := if y+z≤t then min (r-y) (s-z) else 0
  if y=0 ∨ z=0 then 0
  else if y≤B ∧ z≤C then
    if y=B ∧ z=C then A-1 else max A L
  else if B≤y ∧ C≤z then min (A-1) L else L

def endpointH (r s t A B C : ℕ) : ℕ :=
  ∑ y ∈ Icc 1 (max B t), ∑ z ∈ Icc 1 (max C t),
    endpointHRow r s t A B C y z

def endpointAxisGain (r s t A B C : ℕ) : ℕ :=
  let L1 := max r A
  let L2 := max r B
  let L3 := max r C
  jointAxisGain (r+A+B-L1-L2) (s+A+C-L1-L3) (t+B+C-L2-L3)

def endpointBF (r s t A B C : ℕ) : ℕ :=
  1+max r A+max r B+max r C+endpointH r s t A B C+
  Nat.choose r 2+Nat.choose s 2+Nat.choose t 2+
  max (ferrersPlaneDefect r A B) (rankCutPhi r A B)+
  max (ferrersPlaneDefect s A C) (rankCutPhi s A C)+
  max (ferrersPlaneDefect t B C) (rankCutPhi t B C)+
  endpointAxisGain r s t A B C

/-- Exact equality with the manuscript's geometric H; not an assumed lower bound. -/
theorem endpointH_eq_actual (S : CyclicStaircase) (g : Point3) :
    (fullSupportSymbolicH S g).card = endpointH
      (pair12Count S.D) (pair13Count S.D) (pair23Count S.D) g.x g.y g.z := by
  classical
  rw [symbolic_H_card_eq_sum_rows]
  unfold endpointH
  apply sum_congr rfl
  intro y hy
  apply sum_congr rfl
  intro z hz
  exact symbolic_H_row_card S g y z

/-- Full BF, including all three rank cuts and the joint axis gain. -/
theorem endpointBF_eq_actual (S : CyclicStaircase) (g : Point3) :
    fullSupportSymbolicBF S g = endpointBF
      (pair12Count S.D) (pair13Count S.D) (pair23Count S.D) g.x g.y g.z := by
  rw [fullSupportSymbolicBF_eq_weighted,endpointH_eq_actual]
  rfl

private theorem endpoint_data : ∀ i : Fin 8,
    let p := endpointProfile i
    1≤p.z ∧ p.z≤p.y ∧ p.y≤p.x ∧
    endpointTarget p.x p.y p.z=endpointBaseline p.x p.y p.z+endpointK i ∧
    endpointK i+p.x+p.y≤coreCardRows p.x p.y p.z-largeHoleCap p.z+17 := by
  decide

/-- The finite table is checked by the kernel, over exactly 1..6 in each coordinate. -/
theorem eight_profiles_finite : ∀ (i : Fin 8) (a b c : Fin 6),
    let p := endpointProfile i
    p.x+2≤(a.val+1)+(b.val+1)+(c.val+1) →
    endpointTarget p.x p.y p.z+endpointGap i≤
      endpointBF p.x p.y p.z (a.val+1) (b.val+1) (c.val+1) := by
  decide

/-- Exact table domain cardinalities; the eight domains total 1497 triples. -/
theorem eight_profiles_domain_card : ∀ i : Fin 8,
    ((univ : Finset (Fin 6 × (Fin 6 × Fin 6))).filter (fun a =>
      (endpointProfile i).x+2≤(a.1.val+1)+(a.2.1.val+1)+(a.2.2.val+1))).card =
      endpointDomainCard i := by
  decide

theorem eight_profiles_total_domain :
    (∑ i : Fin 8, endpointDomainCard i)=1497 := by decide

/-- Explicit minimizers prove that the displayed lower-bound gaps are exact minima. -/
theorem eight_profiles_minimum_attained : ∀ i : Fin 8,
    let p := endpointProfile i
    let g := endpointWitness i
    (1≤g.x ∧ g.x≤6 ∧ 1≤g.y ∧ g.y≤6 ∧ 1≤g.z ∧ g.z≤6) ∧
    p.x+2≤g.x+g.y+g.z ∧
    endpointBF p.x p.y p.z g.x g.y g.z=endpointTarget p.x p.y p.z+endpointGap i := by
  decide

/-- Symbolic cutoff for all unbounded coordinates, shared by all eight profiles. -/
theorem eight_profiles_large_budget (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (i : Fin 8)
    (hr : pair12Count S.D=(endpointProfile i).x)
    (hs : pair13Count S.D=(endpointProfile i).y)
    (ht : pair23Count S.D=(endpointProfile i).z)
    (hl : 7≤g.x ∨ 7≤g.y ∨ 7≤g.z) :
    fullTarget S≤fullSupportSymbolicBF S g := by
  let p := endpointProfile i
  have hd := endpoint_data i
  change 1≤p.z ∧ p.z≤p.y ∧ p.y≤p.x ∧
    endpointTarget p.x p.y p.z=endpointBaseline p.x p.y p.z+endpointK i ∧
    endpointK i+p.x+p.y≤coreCardRows p.x p.y p.z-largeHoleCap p.z+17 at hd
  have hp := bw_large_coordinate_pressure p.x p.y p.z (endpointK i)
    (coreCardRows p.x p.y p.z-largeHoleCap p.z) g.x g.y g.z
    hd.1 hd.2.1 hd.2.2.1 hf.1 hf.2.1 hf.2.2 hd.2.2.2.2 hl
  have hb := fullSupport_symbolic_BW_core_box_lower S hg hf ho
  rw [fullCore_card_eq_coreCardRows,hr,hs,ht] at hb
  have hbf := fullSupportSymbolicBW_le_BF S g
  have htar : fullTarget S=endpointTarget p.x p.y p.z := by
    simp [fullTarget,endpointTarget,hr,hs,ht,p]
  rw [htar]
  have htarg := hd.2.2.2.1
  unfold endpointBaseline at htarg
  dsimp [p] at hd hp htarg htar ⊢
  omega

/-- The new finite-BF route and common cutoff, under actual staircase hypotheses. -/
theorem eight_profiles_budget (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (i : Fin 8)
    (hr : pair12Count S.D=(endpointProfile i).x)
    (hs : pair13Count S.D=(endpointProfile i).y)
    (ht : pair23Count S.D=(endpointProfile i).z) :
    fullTarget S≤fullSupportSymbolicBF S g := by
  by_cases hl : 7≤g.x ∨ 7≤g.y ∨ 7≤g.z
  · exact eight_profiles_large_budget S hg hf ho i hr hs ht hl
  have hx : g.x≤6 := by omega
  have hy : g.y≤6 := by omega
  have hz : g.z≤6 := by omega
  have hxp := hf.1
  have hyp := hf.2.1
  have hzp := hf.2.2
  let a : Fin 6 := ⟨g.x-1,by omega⟩
  let b : Fin 6 := ⟨g.y-1,by omega⟩
  let c : Fin 6 := ⟨g.z-1,by omega⟩
  have ha : a.val+1=g.x := by dsimp [a]; omega
  have hb : b.val+1=g.y := by dsimp [b]; omega
  have hc : c.val+1=g.z := by dsimp [c]; omega
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  have hfin := eight_profiles_finite i a b c (by simpa [ha,hb,hc,hr] using hcap)
  rw [ha,hb,hc] at hfin
  have heq := endpointBF_eq_actual S g
  rw [hr,hs,ht] at heq
  have htar : fullTarget S=endpointTarget (endpointProfile i).x
      (endpointProfile i).y (endpointProfile i).z := by
    simp [fullTarget,endpointTarget,hr,hs,ht]
  omega

theorem eight_profiles_sharp_indexed (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (i : Fin 8)
    (hr : pair12Count S.D=(endpointProfile i).x)
    (hs : pair13Count S.D=(endpointProfile i).y)
    (ht : pair23Count S.D=(endpointProfile i).z) : fullTarget S≤S.m :=
  (eight_profiles_budget S hg hf ho i hr hs ht).trans
    (fullSupport_symbolic_BF_lower S hg hf ho)

/-- Manuscript-facing disjunction, retaining the eight explicit profiles. -/
theorem eight_profiles_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hq : (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=7 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=6 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=5) ) : fullTarget S≤S.m := by
  rcases hq with ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩ |
    ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩ | ⟨hr,hs,ht⟩
  · exact eight_profiles_sharp_indexed S hg hf ho 0
      (by simpa [endpointProfile] using hr) (by simpa [endpointProfile] using hs)
      (by simpa [endpointProfile] using ht)
  · exact eight_profiles_sharp_indexed S hg hf ho 1
      (by simpa [endpointProfile] using hr) (by simpa [endpointProfile] using hs)
      (by simpa [endpointProfile] using ht)
  · exact eight_profiles_sharp_indexed S hg hf ho 2
      (by simpa [endpointProfile] using hr) (by simpa [endpointProfile] using hs)
      (by simpa [endpointProfile] using ht)
  · exact eight_profiles_sharp_indexed S hg hf ho 3
      (by simpa [endpointProfile] using hr) (by simpa [endpointProfile] using hs)
      (by simpa [endpointProfile] using ht)
  · exact eight_profiles_sharp_indexed S hg hf ho 4
      (by simpa [endpointProfile] using hr) (by simpa [endpointProfile] using hs)
      (by simpa [endpointProfile] using ht)
  · exact eight_profiles_sharp_indexed S hg hf ho 5
      (by simpa [endpointProfile] using hr) (by simpa [endpointProfile] using hs)
      (by simpa [endpointProfile] using ht)
  · exact eight_profiles_sharp_indexed S hg hf ho 6
      (by simpa [endpointProfile] using hr) (by simpa [endpointProfile] using hs)
      (by simpa [endpointProfile] using ht)
  · exact eight_profiles_sharp_indexed S hg hf ho 7
      (by simpa [endpointProfile] using hr) (by simpa [endpointProfile] using hs)
      (by simpa [endpointProfile] using ht)

end NSP3.V03
