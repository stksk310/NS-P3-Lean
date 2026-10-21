import NSP3.LargeTCofinal

namespace NSP3

/-- Arithmetic coordinates of an ordered full-support residual case. -/
structure FullResidualTuple where
  r : ℕ
  s : ℕ
  t : ℕ
deriving DecidableEq, Repr

/-- The baseline appearing in the full-support deficit identity, at raw coordinates. -/
def fullResidualM (r s t : ℕ) : ℕ :=
  3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose t 2

/-- The two arithmetic restrictions used on the `t = 4,5,6` strips. -/
def FullResidualTuple.largeStripArithmetic (q : FullResidualTuple) : Prop :=
  fullResidualM q.r q.s q.t ≤ quarterSquareCeil (q.r + q.s + q.t + 2) ∧
    ((q.r : ℤ) - q.s - q.t + 3) ^ 2 ≤ 4 * (q.s : ℤ) * q.t + 12

/-- The exact six-region arithmetic predicate from the L10 reduction. -/
def FullResidualTuple.IsResidual (q : FullResidualTuple) : Prop :=
  q.t ≤ q.s ∧ q.s ≤ q.r ∧
    ((q.t = 1 ∧ q.r ≤ 3) ∨
     (q.t = 2 ∧ q.r ≤ 9) ∨
     (q.t = 3 ∧ q.r ≤ 15 ∧ q.r ≤ q.s + 5) ∨
     (q.t = 4 ∧ q.s ≤ 8 ∧ q.largeStripArithmetic) ∨
     (q.t = 5 ∧ q.s ≤ 6 ∧ q.largeStripArithmetic) ∨
     (q.t = 6 ∧ q.s = 6 ∧ q.largeStripArithmetic))

instance (q : FullResidualTuple) : Decidable q.largeStripArithmetic := by
  unfold FullResidualTuple.largeStripArithmetic
  infer_instance

instance (q : FullResidualTuple) : Decidable q.IsResidual := by
  unfold FullResidualTuple.IsResidual
  infer_instance

private def fullResidualTupleEmbedding :
    (ℕ × (ℕ × ℕ)) ↪ FullResidualTuple where
  toFun q := FullResidualTuple.mk q.1 q.2.1 q.2.2
  inj' := by
    intro a b h
    apply Prod.ext
    · exact congrArg FullResidualTuple.r h
    · apply Prod.ext
      · exact congrArg FullResidualTuple.s h
      · exact congrArg FullResidualTuple.t h

private def fullResidualTupleBox : Finset FullResidualTuple :=
  ((Finset.range 22).product ((Finset.range 22).product (Finset.range 7))).map
    fullResidualTupleEmbedding

/-- The exact finite arithmetic residual domain. This does not assert realizability. -/
def fullResidualTupleFinset : Finset FullResidualTuple :=
  fullResidualTupleBox.filter FullResidualTuple.IsResidual

@[simp] theorem mem_fullResidualTupleFinset (q : FullResidualTuple) :
    q ∈ fullResidualTupleFinset ↔ q.IsResidual := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    have hres := h
    rcases h with ⟨hts, hsr, hr⟩
    have hrlt : q.r < 22 := by
      rcases hr with h1 | h2 | h3 | h4 | h5 | h6
      · omega
      · omega
      · omega
      · have hs := h4.2.1
        have hsq := h4.2.2.2
        have hnonneg : (0 : ℤ) ≤ ((q.r : ℤ) - q.s - q.t + 3) ^ 2 := sq_nonneg _
        have : q.r ≤ 21 := by nlinarith
        omega
      · have hs := h5.2.1
        have hsq := h5.2.2.2
        have hnonneg : (0 : ℤ) ≤ ((q.r : ℤ) - q.s - q.t + 3) ^ 2 := sq_nonneg _
        have : q.r ≤ 19 := by nlinarith
        omega
      · have hs := h6.2.1
        have hsq := h6.2.2.2
        have hnonneg : (0 : ℤ) ≤ ((q.r : ℤ) - q.s - q.t + 3) ^ 2 := sq_nonneg _
        have : q.r ≤ 21 := by nlinarith
        omega
    have hslt : q.s < 22 := by omega
    have htlt : q.t < 7 := by
      rcases hr with h1 | h2 | h3 | h4 | h5 | h6 <;> omega
    refine ⟨?_, hres⟩
    apply Finset.mem_map.mpr
    refine ⟨(q.r, (q.s, q.t)), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hrlt,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hslt, Finset.mem_range.mpr htlt⟩⟩

/-- Kernel-reduced verification of the exact residual cardinality. -/
theorem fullResidualTupleFinset_card : fullResidualTupleFinset.card = 207 := by
  set_option maxRecDepth 100000 in
    decide

end NSP3
