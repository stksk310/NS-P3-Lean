import P3TorSpike.RegularReductionLocal

noncomputable section
namespace NSP3.TorSpike.RegularReduction
open CategoryTheory
variable {k : Type} [Field k]
variable (S : ShortComplex (ModuleCat.{0} k)) (τ : S ⟶ S)

def coneIncoming : (S.X₂ × S.X₁) →ₗ[k] (S.X₃ × S.X₂) :=
  (-(S.g.hom.comp (LinearMap.fst k S.X₂ S.X₁))).prod
    (τ.τ₂.hom.comp (LinearMap.fst k S.X₂ S.X₁) +
      S.f.hom.comp (LinearMap.snd k S.X₂ S.X₁))

variable {L : Type} [AddCommGroup L] [Module k L]

def coneOutgoing (d₀ : S.X₃ →ₗ[k] L) : (S.X₃ × S.X₂) →ₗ[k] (L × S.X₃) :=
  (-(d₀.comp (LinearMap.fst k S.X₃ S.X₂))).prod
    (τ.τ₃.hom.comp (LinearMap.fst k S.X₃ S.X₂) +
      S.g.hom.comp (LinearMap.snd k S.X₃ S.X₂))

@[simp] theorem coneIncoming_apply (v : S.X₂ × S.X₁) :
    coneIncoming S τ v = (-S.g v.1, τ.τ₂ v.1 + S.f v.2) := rfl

@[simp] theorem coneOutgoing_apply (d₀ : S.X₃ →ₗ[k] L) (v : S.X₃ × S.X₂) :
    coneOutgoing S τ d₀ v = (-d₀ v.1, τ.τ₃ v.1 + S.g v.2) := rfl

theorem cone_squared (d₀ : S.X₃ →ₗ[k] L) (hd₀ : d₀.comp S.g.hom = 0) :
    (coneOutgoing S τ d₀).comp (coneIncoming S τ) = 0 := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · change -d₀ (-S.g v.1) = 0
    simpa using LinearMap.congr_fun hd₀ v.1
  · change τ.τ₃ (-S.g v.1) + S.g (τ.τ₂ v.1 + S.f v.2) = 0
    have hc := congrArg (fun f : S.X₂ ⟶ S.X₃ => f v.1) τ.comm₂₃
    change S.g (τ.τ₂ v.1) = τ.τ₃ (S.g v.1) at hc
    simp only [map_neg,map_add,S.moduleCat_zero_apply,hc,add_zero,neg_add_cancel]

def coneShortComplex (d₀ : S.X₃ →ₗ[k] L) (hd₀ : d₀.comp S.g.hom = 0) :
    ShortComplex (ModuleCat.{0} k) :=
  ShortComplex.moduleCatMk (coneIncoming S τ) (coneOutgoing S τ d₀) (cone_squared S τ d₀ hd₀)

variable {S τ}

/-- Projection from the actual cone to a quotient short complex. -/
def coneProjection {T : ShortComplex (ModuleCat.{0} k)} (φ : S ⟶ T)
    (d₀ : S.X₃ →ₗ[k] L) (hd₀ : d₀.comp S.g.hom = 0)
    (hqt₁ : φ.τ₂.hom.comp τ.τ₂.hom = 0)
    (hqt₀ : φ.τ₃.hom.comp τ.τ₃.hom = 0) : coneShortComplex S τ d₀ hd₀ ⟶ T where
  τ₁ := ModuleCat.ofHom (φ.τ₁.hom.comp (LinearMap.snd k S.X₂ S.X₁))
  τ₂ := ModuleCat.ofHom (φ.τ₂.hom.comp (LinearMap.snd k S.X₃ S.X₂))
  τ₃ := ModuleCat.ofHom (φ.τ₃.hom.comp (LinearMap.snd k L S.X₃))
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change T.f (φ.τ₁ v.2) = φ.τ₂ (τ.τ₂ v.1 + S.f v.2)
    have hc := congrArg (fun f : S.X₁ ⟶ T.X₂ => f v.2) φ.comm₁₂
    have hz := LinearMap.congr_fun hqt₁ v.1
    change φ.τ₂ (τ.τ₂ v.1) = 0 at hz
    simpa [map_add,hz] using hc
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change T.g (φ.τ₂ v.2) = φ.τ₃ (τ.τ₃ v.1 + S.g v.2)
    have hc := congrArg (fun f : S.X₂ ⟶ T.X₃ => f v.2) φ.comm₂₃
    have hz := LinearMap.congr_fun hqt₀ v.1
    change φ.τ₃ (τ.τ₃ v.1) = 0 at hz
    simpa [map_add,hz] using hc

/-- The cone of a degreewise injective multiplication map has the homology of its quotient.
All hypotheses concern the original differentials and ordinary kernels/ranges. -/
def coneQuotientHomologyEquiv {T : ShortComplex (ModuleCat.{0} k)} (φ : S ⟶ T)
    (d₀ : S.X₃ →ₗ[k] L) (hd₀ : d₀.comp S.g.hom = 0) (tPrev : L →ₗ[k] L)
    (hcomm : d₀.comp τ.τ₃.hom = tPrev.comp d₀)
    (hinj₀ : Function.Injective τ.τ₃) (hinjPrev : Function.Injective tPrev)
    (hex₁ : LinearMap.range τ.τ₂.hom = LinearMap.ker φ.τ₂.hom)
    (hex₀ : LinearMap.range τ.τ₃.hom = LinearMap.ker φ.τ₃.hom)
    (hsurj₁ : Function.Surjective φ.τ₂) (hsurj₂ : Function.Surjective φ.τ₁) :
    (coneShortComplex S τ d₀ hd₀).homology ≃ₗ[k] T.homology := by
  have hqt₁ : φ.τ₂.hom.comp τ.τ₂.hom = 0 := by
    apply LinearMap.range_le_ker_iff.mp
    exact hex₁.le
  have hqt₀ : φ.τ₃.hom.comp τ.τ₃.hom = 0 := by
    apply LinearMap.range_le_ker_iff.mp
    exact hex₀.le
  apply homologyEquiv (coneProjection (τ := τ) φ d₀ hd₀ hqt₁ hqt₀)
  · intro y hy
    obtain ⟨v,hv⟩ := hsurj₁ y
    have hgv : S.g v ∈ LinearMap.range τ.τ₃.hom := by
      rw [hex₀]
      have hc := congrArg (fun f : S.X₂ ⟶ T.X₃ => f v) φ.comm₂₃
      change T.g (φ.τ₂ v) = φ.τ₃ (S.g v) at hc
      change φ.τ₃ (S.g v) = 0
      rw [← hc,hv,hy]
    obtain ⟨x,hx⟩ := hgv
    have hdx : d₀ x = 0 := by
      apply hinjPrev
      have hc := LinearMap.congr_fun hcomm x
      have hz : d₀ (S.g v) = 0 := LinearMap.congr_fun hd₀ v
      change d₀ (τ.τ₃ x) = tPrev (d₀ x) at hc
      simpa [hx,hz] using hc.symm
    refine ⟨(-x,v),?_,hv⟩
    apply Prod.ext
    · change -d₀ (-x) = 0
      simp [hdx]
    · change τ.τ₃ (-x) + S.g v = 0
      simp [map_neg,hx]
  · rintro ⟨x,v⟩ hcycle ⟨b,hb⟩
    obtain ⟨w,hw⟩ := hsurj₂ b
    have hv : v - S.f w ∈ LinearMap.range τ.τ₂.hom := by
      rw [hex₁]
      change φ.τ₂ (v - S.f w) = 0
      have hc := congrArg (fun f : S.X₁ ⟶ T.X₂ => f w) φ.comm₁₂
      change T.f (φ.τ₁ w) = φ.τ₂ (S.f w) at hc
      change T.f b = φ.τ₂ v at hb
      rw [map_sub, ← hc,hw,hb,sub_self]
    obtain ⟨z,hz⟩ := hv
    refine ⟨(z,w),?_⟩
    apply Prod.ext
    · change -S.g z = x
      apply hinj₀
      have hc := congrArg (fun f : S.X₂ ⟶ S.X₃ => f z) τ.comm₂₃
      change S.g (τ.τ₂ z) = τ.τ₃ (S.g z) at hc
      have hcy : τ.τ₃ x + S.g v = 0 := congrArg Prod.snd hcycle
      calc
        τ.τ₃ (-S.g z) = -S.g (τ.τ₂ z) := by rw [map_neg, ← hc]
        _ = -S.g (v - S.f w) := by rw [hz]
        _ = τ.τ₃ x := by
          simp only [map_sub,S.moduleCat_zero_apply,sub_zero]
          exact (eq_neg_iff_add_eq_zero.mpr hcy).symm
    · change τ.τ₂ z + S.f w = v
      rw [hz]
      abel

end NSP3.TorSpike.RegularReduction
