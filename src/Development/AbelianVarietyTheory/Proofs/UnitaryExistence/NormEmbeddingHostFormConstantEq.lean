import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralAlgebraicFramedPointExists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEquivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsInfEmb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReindexUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelM
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentSingleAdd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLinearApproxTower
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SelfDualLatticeOccurs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecondStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingThird
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.LevelHalf

theorem prime_of_between {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2) (J : Ideal (𝓞 K))
    (hle : Ideal.span {(p : 𝓞 K)} ≤ J) (h1 : J ≠ ⊤) (h2 : J ≠ Ideal.span {(p : 𝓞 K)}) :
    J.IsPrime ∧ J ≠ ⊥ := by
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 hle
  have hN' := congrArg Ideal.absNorm hC
  rw [map_mul, hN] at hN'
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN'.symm)
  have hi1 : i = 1 := by
    interval_cases i
    · rw [pow_zero, Ideal.absNorm_eq_one_iff] at hieq; exact absurd hieq h1
    · rfl
    · exfalso
      rw [hieq] at hN'
      have hc : Ideal.absNorm C = 1 :=
        Nat.eq_of_mul_eq_mul_left (by have := hp.pos; positivity) (hN'.symm.trans (mul_one _).symm)
      rw [Ideal.absNorm_eq_one_iff] at hc
      rw [hc, Ideal.mul_top] at hC
      exact h2 hC.symm
  rw [hi1, pow_one] at hieq
  refine ⟨Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.prime.irreducible), ?_⟩
  intro h
  rw [h, Ideal.absNorm_bot] at hieq
  exact hp.ne_zero hieq.symm

theorem eq_sup_mul_sup {S : Type} [CommRing S] (I : Ideal S) (a b : S) (hab : IsCoprime a b)
    (h : a * b ∈ I) : I = (I ⊔ Ideal.span {a}) * (I ⊔ Ideal.span {b}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, v, huv⟩ := hab
    have e : x = (u * a) * x + x * (v * b) := by linear_combination (-x) * huv
    rw [e]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
        (Ideal.mem_sup_left hx))
      (Ideal.mul_mem_mul (Ideal.mem_sup_left hx)
        (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))))
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
    refine sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right ?_)
    rwa [Ideal.span_singleton_le_iff_mem]

theorem sup_ne {S : Type} [CommRing S] (σ : S →+* S) (I : Ideal S) (p : ℕ)
    (hp : Ideal.span {(p : S)} ≠ ⊤) (hm : I * I.map σ ≤ Ideal.span {(p : S)}) (hc : I ⊔ I.map σ = ⊤) :
    I ⊔ Ideal.span {(p : S)} ≠ ⊤ ∧ I ⊔ Ideal.span {(p : S)} ≠ Ideal.span {(p : S)} := by
  have hσ : (Ideal.span {(p : S)}).map σ = Ideal.span {(p : S)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  constructor
  · intro h
    have h' : I.map σ ⊔ Ideal.span {(p : S)} = ⊤ := by
      have := congrArg (Ideal.map σ) h
      rwa [Ideal.map_sup, hσ, Ideal.map_top] at this
    have h3 : IsCoprime (I * I.map σ) (Ideal.span {(p : S)}) :=
      IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.2 h) (Ideal.isCoprime_iff_sup_eq.2 h')
    rw [Ideal.isCoprime_iff_sup_eq, sup_eq_right.2 hm] at h3
    exact hp h3
  · intro h
    have hI : I ≤ Ideal.span {(p : S)} := sup_eq_right.1 h
    have hI' : I.map σ ≤ Ideal.span {(p : S)} := hσ ▸ Ideal.map_mono hI
    exact hp (top_le_iff.1 (hc ▸ sup_le hI hI'))

theorem half_eq_prod : ∀ (D : D7) (Q : Par D), Q.Pins → ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧ Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  intro D Q hQ
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hQ.2.1.1
  have hrt : (Q.H.rt : D.host.E) = D.host.sqrtMinusD := hQ.1.2.1
  have hw : Q.H.w0 = w0E D := by
    have h1 := Q.H.two_weight_eq_one_add_root
    have h2 := two_w0E D
    have h3 : Q.H.rt = rtE D := RingOfIntegers.ext hrt
    rw [h3, ← h2] at h1
    exact mul_left_cancel₀ two_ne_zero h1
  set f := algebraMap (𝓞 D.host.K) (𝓞 D.host.E) with hf
  set I := Q.l.Mb with hI
  have hIm : (I.comap f).map f = I := by
    apply le_antisymm Ideal.map_comap_le
    refine Q.l.fromK.le.trans ?_
    rw [Ideal.span_le]
    rintro a ⟨ha, ha'⟩
    have hr : a ∈ (f.toIntAlgHom).range := by
      refine (Algebra.adjoin_le ?_ : Algebra.adjoin ℤ {Q.H.w0} ≤ (f.toIntAlgHom).range) ha'
      rw [Set.singleton_subset_iff, hw]
      exact ⟨LPb.w0K D, LPb.algebraMap_w0K D⟩
    obtain ⟨y, hy⟩ := hr
    have hy' : f y = a := hy
    rw [← hy'] at ha ⊢
    exact Ideal.mem_map_of_mem f ha
  have hprod := Q.l.prod
  rw [hM, Nat.cast_mul] at hprod
  have hmap : ∀ p : ℕ, (I.comap f ⊔ Ideal.span {(p : 𝓞 D.host.K)}).map f = I ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
    intro p
    rw [Ideal.map_sup, hIm, Ideal.map_span, Set.image_singleton, map_natCast]
  have hspan : ∀ p : ℕ, (Ideal.span {(p : 𝓞 D.host.K)}).map f = Ideal.span {(p : 𝓞 D.host.E)} := by
    intro p
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have key : ∀ k : Fin 2, (I.comap f ⊔ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.K)}).IsPrime ∧
      (I.comap f ⊔ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.K)}) ≠ ⊥ := by
    intro k
    have hm : I * I.map (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} := by
      rw [hI, hprod, Ideal.span_singleton_le_span_singleton]
      fin_cases k
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨h1, h2⟩ := sup_ne _ I _ (LPb.span_p_ne_top D (D.host.g_prime k)) hm Q.l.coprime
    refine prime_of_between (D.host.g_prime k) (LPb.absNorm_span_p D _) _ le_sup_right ?_ ?_
    · intro h
      apply h1
      rw [← hmap, h, Ideal.map_top]
    · intro h
      apply h2
      rw [← hmap, h, hspan]
  refine ⟨fun k => ⟨_, (key k).1, (key k).2⟩, fun k => Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), ?_⟩
  rw [Fin.prod_univ_two]
  show I = (I.comap f ⊔ _).map f * (I.comap f ⊔ _).map f
  rw [hmap, hmap]
  apply eq_sup_mul_sup
  · have := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using this.map (Int.castRingHom (𝓞 D.host.E))
  · rw [← Ideal.span_singleton_le_iff_mem, ← hprod]
    exact Ideal.mul_le_left

end GlobalTheory.LevelHalf
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.CuspSqInt

open MeasureTheory
open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) : Frame Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) (τ : Ψ) : mat (frInv b) τ = (mat b τ)⁻¹ := rfl

theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

theorem eq_zero_of_orbit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, P (lact γ x) = X.χ la γ * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hz : rmul (lact γ x) b ∈ X.dom) (h0 : P (rmul (lact γ x) b) = 0) : P x = 0 := by
  classical
  have hdet : ∀ τ, (mat b τ).det ≠ 0 := fun τ => (hb τ).1
  have hbinv : frInv b ∈ Bor X.Ψ r := by
    intro τ
    refine ⟨?_, fun a c hca => ?_⟩
    · rw [mat_frInv]
      exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (hdet τ))).ne_zero
    · haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.2 (hdet τ))
      have ht : Matrix.BlockTriangular (mat b τ) id := fun i j hij => (hb τ).2 i j hij
      have := Matrix.blockTriangular_inv_of_blockTriangular ht hca
      rw [← mat_frInv] at this
      exact this
  have hcancel : rmul (rmul (lact γ x) b) (frInv b) = lact γ x := by
    funext τ
    have e : mat (rmul (rmul (lact γ x) b) (frInv b)) τ = mat (lact γ x) τ := by
      rw [mat_rmul, mat_rmul, mat_frInv]
      exact Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 (hdet τ))
    exact Matrix.of.injective e
  have h1 : P (lact γ x) = 0 := by
    have := hB _ hz (frInv b) hbinv
    rw [hcancel, h0, mul_zero] at this
    exact this
  rw [hΓ γ hγ x hx] at h1
  obtain ⟨n, hn, hχ⟩ := X.χ_fin la
  have hne : X.χ la γ ≠ 0 := by
    intro h
    have := hχ γ hγ
    rw [h, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact (mul_eq_zero.1 h1).resolve_left hne

theorem eqv_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X}
    (hP : P ∈ holSub X la) :
    (∀ k, ∀ x ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, P k (rmul x b) = bchar (la k) b * P k x) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x) := by
  induction hP using Submodule.span_induction with
  | mem P hP => exact ⟨fun k => (hP k).1.1.2.1, fun k => (hP k).1.1.2.2⟩
  | zero => exact ⟨fun k x _ b _ => by simp, fun k γ _ x _ => by simp⟩
  | add P Q _ _ h1 h2 =>
    exact ⟨fun k x hx b hb => by simp only [Pi.add_apply]; rw [h1.1 k x hx b hb, h2.1 k x hx b hb, mul_add],
      fun k γ hγ x hx => by simp only [Pi.add_apply]; rw [h1.2 k γ hγ x hx, h2.2 k γ hγ x hx, mul_add]⟩
  | smul a P _ h1 =>
    exact ⟨fun k x hx b hb => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h1.1 k x hx b hb]; ring,
      fun k γ hγ x hx => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h1.2 k γ hγ x hx]; ring⟩

variable {D : D7} {Comp : Type}

section Defs

variable {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
  (mu : GA D V → ℂ)

def AdelAut : Prop :=
  ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)

def QuotSupp : Prop :=
  ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → onQ V φ =ᵐ[muQ1 V] 0 → ∀ g, φ g = 0

variable {V dict mu}

theorem adelAut_holSub (h : AdelAut V dict mu) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  induction hP using Submodule.span_induction with
  | mem P hP => exact h la P hP
  | zero => exact ⟨fun γ _ g => by simp, by rw [map_zero]; exact continuous_const⟩
  | add P Q _ _ h1 h2 =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · rw [map_add]; simp only [Pi.add_apply]; rw [h1.1 γ hγ g, h2.1 γ hγ g]
    · rw [map_add]; exact h1.2.add h2.2
  | smul a P _ h1 =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · rw [map_smul]; simp only [Pi.smul_apply]; rw [h1.1 γ hγ g]
    · rw [map_smul]; exact h1.2.const_smul a

theorem onQ_eq_lift (φ : GA D V → ℂ) (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    onQ V φ = Quotient.lift φ (fun a b hab => by
      have h' : b * a⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.1 hab
      have := hL _ h' a
      rw [inv_mul_cancel_right] at this
      exact this.symm) := by
  funext q
  show φ q.out = _
  conv_rhs => rw [← Quotient.out_eq q]
  rfl

theorem adelMeas_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ}
    (h : AdelAut V dict mu) : AdelMeas U σ V dict mu := by
  intro la P hP
  obtain ⟨hL, hC⟩ := h la P hP
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [onQ_eq_lift _ hL]
  refine Measurable.aestronglyMeasurable ?_
  exact measurable_from_quotient.2 hC.measurable

theorem aeDom_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hQ : QuotSupp V) (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) :
    AeDom U σ V dict mu := by
  intro la P hP hae k x hx
  have hA' := adelAut_holSub hA la hP
  have hz : ∀ g, adel V dict mu P g = 0 := hQ _ hA'.2 hA'.1 hae
  have hEq := eqv_holSub (U σ).X la hP
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hd.2.2.2.2.1 k x hx
  have hdom := hd.2.2.2.1 g
  have h0 := hz g
  change mu g * P (dict g).1 (dict g).2 = 0 at h0
  rw [hg] at h0 hdom
  have hmu0 : mu g ≠ 0 := by
    intro h
    have := hmu.2.1 g
    rw [h, norm_zero] at this
    exact zero_ne_one this
  exact eq_zero_of_orbit _ (la k) (P k) (hEq.1 k) (hEq.2 k) hx hγ hb hdom ((mul_eq_zero.1 h0).resolve_left hmu0)

end Defs

theorem volPair_of_tie (hT : VolTieG D) (V : HSp D) (hs : V.SigOK) : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  obtain ⟨⟨μ, hμ⟩, h2⟩ := hT V hs
  obtain ⟨⟨𝓕, h𝓕⟩, _⟩ := h2 μ hμ
  exact ⟨(μ, 𝓕), hμ, h𝓕⟩

theorem quotSupp_of (V : HSp D) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    QuotSupp V := by
  intro φ hc hL hae g0
  have hvp : IsVolPair D V (volPair V).1 (volPair V).2 := by
    unfold volPair
    rw [dif_pos hP]
    exact hP.choose_spec
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI : (volPair V).1.IsHaarMeasure := hvp.1.1
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) (volPair V).1

  have h1 : onQ V φ =ᵐ[muQ V] 0 := by
    have hq : muQ1 V = (muQ V Set.univ)⁻¹ • muQ V := by
      unfold muQ1; rw [if_pos (show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ from hV)]
    rw [hq] at hae
    rw [Filter.EventuallyEq, ae_iff] at hae ⊢
    rw [Measure.smul_apply, smul_eq_mul] at hae
    exact (mul_eq_zero.1 hae).resolve_left (ENNReal.inv_ne_zero.2 hV.2)

  have h2 : ∀ᵐ g ∂((volPair V).1.restrict (volPair V).2), φ g = 0 := by
    have hm : AEMeasurable (autMk V) ((volPair V).1.restrict (volPair V).2) :=
      (measurable_quotient_mk'' (s := QuotientGroup.rightRel (GQ V))).aemeasurable
    have := ae_of_ae_map hm (show ∀ᵐ q ∂(muQ V), onQ V φ q = (0 : AutQ V → ℂ) q from h1)
    filter_upwards [this] with g hg
    rw [onQ_eq_lift φ hL] at hg
    exact hg
  let t : Set (GA D V) := {g | φ g ≠ 0}
  have ht : IsOpen t := hc.isOpen_preimage _ isOpen_ne
  have htm : MeasurableSet t := ht.measurableSet
  have h3 : (volPair V).1 (t ∩ (volPair V).2) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h2
  have hinv : ∀ γ : GQ V, γ • t = t := by
    intro γ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show φ (γ⁻¹ • x) ≠ 0 ↔ φ x ≠ 0
    rw [Subgroup.smul_def, smul_eq_mul, hL _ (γ⁻¹).2 x]
  have h4 : (volPair V).1 t = 0 := hvp.2.measure_zero_of_invariant t hinv h3
  have h5 : t = ∅ := (ht.measure_eq_zero_iff (volPair V).1).1 h4
  by_contra hne
  have : g0 ∈ t := hne
  rw [h5] at this
  exact this

theorem adel_leftInv_triv {X : Comp → Data E r} {V : HSp D} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} (hχ : ∀ k la γ, (X k).χ la γ = 1)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu)
    (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : IsHolCusp X la P) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g := by
  intro γ hγ g
  obtain ⟨γ', hγ', he⟩ := hd γ hγ g
  have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hdom g)
  show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
  rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
  show mu g * P (dict g).1 (lact γ' (dict g).2) = _
  rw [hE, hχ, one_mul]

theorem adelCont_of {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} (hχ : ∀ k la γ, (X k).χ la γ = 1) (hL : ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : Comp) (x : GA D V → Frame (X k).Ψ r), ContinuousOn x N ∧
      ∀ g ∈ N, x g ∈ (X k).dom ∧ ∃ γ ∈ (X k).Γ, dict g = ⟨k, lact γ (x g)⟩) (hm : Continuous mu) :
    ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P → Continuous (adel V dict mu P) := by
  intro la P hP
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
  have hsec : (X k).IsSec (la k) (P k) := (hP k).1.1
  have hPc : ContinuousOn (P k) (X k).dom := hsec.1.continuousOn
  have hc : ContinuousOn (fun g => mu g * P k (x g)) N :=
    hm.continuousOn.mul (hPc.comp hx fun g hg => (hs g hg).1)
  have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
    filter_upwards [hN] with g hg
    obtain ⟨hd, γ, hγ, he⟩ := hs g hg
    show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
    rw [he]
    show mu g * P k (x g) = mu g * P k (lact γ (x g))
    rw [hsec.2.2 γ hγ (x g) hd, hχ, one_mul]
  exact (hc.continuousAt hN).congr heq

end Adelic

theorem cusp_l2_and_definite : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) (Kf : Subgroup (GA D V)) (th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r), VolTieG D → V.SigOK → GoodEmb c σ → (∀ k la γ, ((U σ).X k).χ la γ = 1) → DictIsUnif V dict Kf th hr → MuUnit V dict mu → Continuous mu → (∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D V → Frame ((U σ).X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ ((U σ).X k).dom ∧ ∃ γ ∈ ((U σ).X k).Γ, dict g = ⟨k, lact γ (x g)⟩) → SupDef Xo c U → ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  intro D H Dw l Xo c r U σ V dict mu Kf th hr hT hs hσ hχ hd hm hmc hL hsup
  have hA : AdelAut V dict mu := fun la P hP =>
    ⟨adel_leftInv_triv hχ hd.1 hd.2.2.2.1 hm la hP, adelCont_of hχ hL hmc la P hP⟩
  have h := cusp_L2_of_measurable hσ (dict_dom_of hd) hm (adelMeas_of_aut Xo c hA)
  exact ⟨h, l2Def_of_cusp hσ hsup (aeDom_of_aut Xo c hA
    (quotSupp_of V (finVol_of_volTie hT V hs) (volPair_of_tie hT V hs)) hm hd) h⟩

end GlobalTheory.CuspSqInt
end
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

theorem lat_cusp_expo : GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → FJ.LatZ M.X (WeightFamilies.rho D j) ∧ FJ.CuNeF M.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch M.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) := by
  intro HN D Q hQ j hj σ' g ty F _ _ M io th x₀ hM
  refine ⟨GlobalTheory.CuspCentre.latZ _ _ _ _ _, fun k => ?_, ?_⟩
  · have hp : (M.X k).p0 = D.R.m - j := ((hM.1.type k).1).trans (hQ.2.2.2 j hj).2.1
    have hρ : WeightFamilies.rho D j = D.R.m - j := rfl
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hk := D.R.m_add_three_le_k
    have h1 := hj.1
    have h2 := hj.2
    exact GlobalTheory.CuspExist.nonempty_cuspFD HN _ _ _ _ (by omega) (by omega) (by omega)
  · rw [← hQ.2.1.1]
    exact GlobalTheory.ExpoModels.expoMatch_models _ _ _ _ _ _ _ _ F _ M _ hM.1 hQ.2.1.2

end GlobalTheory.RecDict
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

open scoped Matrix nonZeroDivisors

theorem genus_traceIdeal (E : Type) [Field E] [NumberField E] (ξ : E) (hξ : ξ ≠ 0) :
    ∃ J : FractionalIdeal (𝓞 E)⁰ E, J ≠ 0 ∧
      ∀ z : E, z ∈ J ↔ ∀ s : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (ξ * (z * (s : E))) = k := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  refine ⟨FractionalIdeal.spanSingleton _ ξ⁻¹ * FractionalIdeal.dual ℤ ℚ 1,
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 (inv_ne_zero hξ))
      (FractionalIdeal.dual_ne_zero ℤ ℚ h1), fun z => ⟨fun hz s => ?_, fun hz => ?_⟩⟩
  · obtain ⟨y, hy, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hz
    rw [FractionalIdeal.mem_dual h1] at hy
    obtain ⟨k, hk⟩ := hy (s : E) ((FractionalIdeal.mem_one_iff _).2 ⟨s, rfl⟩)
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast] at hk
    rw [hk]
    congr 1
    field_simp
  · refine FractionalIdeal.mem_singleton_mul.2 ⟨ξ * z, ?_, by field_simp⟩
    rw [FractionalIdeal.mem_dual h1]
    intro a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := hz s
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk, mul_assoc]

theorem genus_trace_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (ξ : E) (J : FractionalIdeal (𝓞 E)⁰ E)
    (hJ : ∀ z : E, z ∈ J ↔ ∀ s : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (ξ * (z * (s : E))) = k)
    (L : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    (∀ y ∈ L, herm G v y ∈ J) ↔ ∀ y ∈ L, ∃ k : ℤ, Algebra.trace ℚ E (ξ * herm G v y) = k := by
  constructor
  · intro h y hy
    simpa using (hJ _).1 (h y hy) 1
  · intro h y hy
    refine (hJ _).2 fun s => ?_
    have hi : IsIntegral ℤ (cc (s : E)) :=
      s.isIntegral_coe.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)
    have hcc : cc (cc (s : E)) = s := IsCMField.complexConj_apply_apply E _
    have := h _ (L.smul_mem (⟨cc (s : E), hi⟩ : 𝓞 E) hy)
    change ∃ k : ℤ, Algebra.trace ℚ E (ξ * herm G v (cc (s : E) • y)) = k at this
    rwa [GlobalTheory.HermModel.herm_smul_right, hcc] at this

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem genus_hermA_shift (N : ℕ) (x y w w' : Fin n → AdLat.RA F E) :
    AdLat.hermA c G (x + N • w) (y + N • w') =
      AdLat.hermA c G x y + N • (AdLat.hermA c G w (y + N • w') + AdLat.hermA c G x w') := by
  simp only [AdLat.hermA, Pi.add_apply, Pi.smul_apply, map_add, map_nsmul, smul_add, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [nsmul_eq_mul]
  ring

theorem genus_fv_mulVec (γ : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    AdLat.fv F (γ *ᵥ v) = γ.map (inclR (F := F) (Af F)) *ᵥ AdLat.fv F v := by
  funext i
  exact RingHom.map_mulVec (inclR (F := F) (Af F)) γ v i

end

theorem genus_translate (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (c : E ≃ₐ[F] E) (hc : ∀ x, c x = cc x) (G : Matrix (Fin n) (Fin n) E) (hG : ∀ a b, cc (G a b) = G b a)
    (hdet : G.det ≠ 0) (ξ : E) (hξ : ξ ≠ 0) (L Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hsd : ∀ v, (∀ y ∈ L, ∃ k : ℤ, Algebra.trace ℚ E (ξ * herm G v y) = k) ↔ v ∈ L)
    (g : GL (Fin n) (AdLat.RA F E))
    (hg : ∀ x y, AdLat.hermA c G (g.1 *ᵥ x) (g.1 *ᵥ y) = AdLat.hermA c G x y)
    (hΛ : (Λ : Set (Fin n → E)) = AdLat.latOf F g.1 L) :
    Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      (∀ v, (∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (ξ * herm G v y) = k) ↔ v ∈ Λ) ∧
      ∃ f : ℕ → (L →ₗ[𝓞 E] Λ),
        (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ AdLat.hat F (L : Set (Fin n → E)),
          AdLat.fv F (f N a : Fin n → E) = g.1 *ᵥ (AdLat.fv F (a : Fin n → E) + N • w)) ∧
        (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) ∧
        (∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v) ∧
        ∀ N : ℕ, 0 < N → ∀ a a' : L, ∃ z : ℤ, Algebra.trace ℚ E (ξ * herm G (f N a) (f N a')) -
          Algebra.trace ℚ E (ξ * herm G a a') = N * z := by
  obtain ⟨J, hJ0, hJ⟩ := genus_traceIdeal E ξ hξ
  have hh : ∀ x y : Fin n → E, (∑ a, ∑ b, x a * G a b * c (y b)) = herm G x y := fun x y => by
    simp only [hc, herm]
  have hcc : ∀ x, c (c x) = x := fun x => by
    rw [hc, hc]; exact IsCMField.complexConj_apply_apply E _
  have hG' : ∀ a b, c (G a b) = G b a := fun a b => by rw [hc, hG]
  have hL : ∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L := fun v => by
    simp only [hh]
    rw [genus_trace_iff G ξ J hJ, hsd]
  obtain ⟨Λ', h1, hΛfg, hΛsp, -⟩ := AdLat.exists_lattice_latOf F E n L g hfg hsp
  obtain rfl : Λ = Λ' := SetLike.coe_injective (hΛ.trans h1.symm)
  obtain ⟨f, hf1, hf2, hf3⟩ := AdLat.exists_linear_approx_tower F E n L g Λ hfg hsp hΛ
  refine ⟨hΛfg, hΛsp, fun v => ?_, f, hf1, hf2, hf3, fun N hN a a' => ?_⟩
  · have := AdLat.latOf_selfDual F E n L c G J g hfg hsp hcc hG' hdet hJ0 hL hg v
    simp only [hh, ← hΛ, SetLike.mem_coe] at this
    rw [← genus_trace_iff G ξ J hJ, this]
  · obtain ⟨w, hw, e⟩ := hf1 N hN a
    obtain ⟨w', hw', e'⟩ := hf1 N hN a'
    have hd := AdLat.hat_selfDual F E n L c G J hfg hsp hcc hG' hdet hJ0 hL
    have hr := (AdLat.hat_rational_points_and_approx F E n L hfg hsp).1
    have hm : ∀ z ∈ AdLat.hat F (L : Set (Fin n → E)), ∀ z' ∈ AdLat.hat F (L : Set (Fin n → E)),
        AdLat.hermA c G z z' ∈ AdLat.hat1 F (J : Set E) := fun z hz z' hz' =>
      AdLat.adelicHermitianFormGalois_mem_of_mem_completion c G ((hd z).2 hz) hz'
    have hs := add_mem (hm w hw _ (add_mem ((hr _).2 a'.2) (nsmul_mem hw' N))) (hm _ ((hr _).2 a.2) w' hw')
    have key := genus_hermA_shift c G N (AdLat.fv F (a : Fin n → E)) (AdLat.fv F (a' : Fin n → E)) w w'
    rw [← hg, ← e, ← e', AdLat.hermA_fv_fv, AdLat.hermA_fv_fv, hh, hh] at key
    have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    set t : E := (N : E)⁻¹ * (herm G (f N a) (f N a') - herm G a a') with ht
    have ht' : N • t = herm G (f N a) (f N a') - herm G a a' := by
      rw [nsmul_eq_mul, ht, mul_inv_cancel_left₀ hN']
    have htJ : t ∈ J := by
      rw [← (AdLat.adelicCompletion_fractionalIdeal_properties F E).2.1]
      convert hs using 1
      apply smul_right_injective _ hNF
      simp only [Nat.cast_smul_eq_nsmul]
      rw [← TensorProduct.tmul_smul, ht', TensorProduct.tmul_sub, key, add_sub_cancel_left]
    obtain ⟨k, hk⟩ := (hJ t).1 htJ 1
    refine ⟨k, ?_⟩
    rw [← map_sub, ← mul_sub, ← ht', ← hk, mul_smul_comm, map_nsmul, nsmul_eq_mul]
    simp

theorem genus_mem_UJ {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (σ : E →+* E) (hσ : ∀ x, σ x = cc x)
    (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E)
    (h : ∀ u v, herm (-J.transpose) (γ.1 *ᵥ u) (γ.1 *ᵥ v) = herm (-J.transpose) u v) : γ ∈ Formalism.UG.UJ σ J := by
  change Formalism.UG.cT _ _ * _ * _ = _
  ext i j
  have h := h (Pi.single j 1) (Pi.single i 1)
  simp only [herm, ← hσ, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.neg_apply,
    Matrix.transpose_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_inj] at h
  simp only [Pi.single_apply, apply_ite σ,
    map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem genus_bc_mem_HR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E)
    (h : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) : Formalism.UG.bc (inclR (F := F) R) γ ∈ HR R σ J := by
  have h0 : Formalism.UG.cT (σ : E →+* E) γ.1 * J * γ.1 = J := h
  have h3 : (Formalism.UG.cT (σ : E →+* E) γ.1).map (inclR (F := F) R) =
      Formalism.UG.cT (sigR R σ) (γ.1.map (inclR (F := F) R)) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR]
  have h4 := congrArg (fun m => m.map (inclR (F := F) R)) h0
  simp only [Matrix.map_mul, h3] at h4
  exact h4

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genus_exists_rat (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E)
    (h : ∀ u v, herm (-V.gram.transpose) (γ.1 *ᵥ u) (γ.1 *ᵥ v) = herm (-V.gram.transpose) u v) :
    ∃ γ' ∈ GQ V, (finHom V γ').1 = γ.1.map (inclR (F := D.host.F) (Af D.host.F)) := by
  have h1 := genus_mem_UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (fun _ => rfl) V.gram γ h
  refine ⟨(⟨_, genus_bc_mem_HR (AF D.host.F) D.sp.cm.sig V.gram γ h1⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram),
    ⟨γ, h1, rfl⟩, ?_⟩
  ext i j
  rfl

theorem genus_mulVec_inj {A : Type} [CommRing A] {n : ℕ} (g : GL (Fin n) A) {u v : Fin n → A}
    (h : g.1 *ᵥ u = g.1 *ᵥ v) : u = v := by
  have := congrArg (fun t => (g⁻¹).1 *ᵥ t) h
  simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using this

theorem genus_sub_eq {A : Type} [AddCommGroup A] (N : ℕ) (x e y w : A) (h : y + N • w = x + N • e) :
    x - y = N • (w - e) := by
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← h, add_comm]

set_option maxHeartbeats 800000 in

theorem genus_marked (hH : GlobalTheory.Published.HasseNormSt) (D : D7) (V : HSp D)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (hA : l.A = 1) (hσ : σ' (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H Dw.p Dw.q ty) {r : ℕ} (hr : V.rank = r) (M : GlobalTheory.FrameUnif.ModelsOf F r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) (h : GA D V) :
    ∃ p, MarkSpec M V hr io th x₀ h p := by
  subst hr
  obtain ⟨hbase, hW, ⟨hinj, hrange⟩, hEF, -, -⟩ := hR
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  let X0 := M.X ⟨0, F.n_pos⟩
  have hGm : X0.Gm = -V.gram.transpose := (hW _).1
  have hξ0 : X0.ξ0 = -D.host.xi0 := (hW _).2
  have hξ : -(-D.host.xi0) ≠ 0 := by
    rw [← hξ0]
    exact neg_ne_zero.2 X0.ξ0_ne
  have hξ' : cc (-(-D.host.xi0)) = -(-(-D.host.xi0)) := by
    have h := X0.ξ0_im
    rw [hξ0] at h
    unfold cc at h ⊢
    rw [map_neg, h]
  have hφ : Function.Injective io ∧ Submodule.span D.host.E (Set.range io) = ⊤ ∧
      (∀ a b, cc ((-V.gram.transpose) a b) = (-V.gram.transpose) b a) ∧ (-V.gram.transpose).det ≠ 0 ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
        (-(-D.host.xi0) * herm (-V.gram.transpose) (io x) (io y)) :=
    ⟨hinj, hsp, hGm ▸ X0.Gm_herm, hGm ▸ X0.Gm_det, hEF⟩
  have hsd := (GlobalTheory.HermModel.rank_integral_selfDual _ H Dw V.rank _ _ io hξ' hφ).2.2.2
  have hu : ∀ x y, AdLat.hermA (LevelHalf.conjEquiv D.sp.cm) (-V.gram.transpose) ((finHom V h).1 *ᵥ x)
      ((finHom V h).1 *ᵥ y) = AdLat.hermA (LevelHalf.conjEquiv D.sp.cm) (-V.gram.transpose) x y := by
    intro x y
    have := LevelHalf.hermA_unitary D.sp.cm V.gram _ (LevelHalf.finHom_mem V h) x y
    simp only [AdLat.hermA, Matrix.neg_apply, TensorProduct.tmul_neg, mul_neg, neg_mul, Finset.sum_neg_distrib,
      neg_inj] at this ⊢
    exact this
  obtain ⟨hΛfg, hΛsp, hΛsd, f, hf1, hf2, hf3, hf4⟩ := genus_translate D.host.F D.host.E V.rank
    (LevelHalf.conjEquiv D.sp.cm) (fun _ => rfl) (-V.gram.transpose) hφ.2.2.1 hφ.2.2.2.1 _ hξ
    (LinearMap.range io) (latG V h) hfg hsp
    (fun v => by
      rw [← hsd v]
      exact ⟨fun hv y => hv _ ⟨y, rfl⟩, by rintro hv _ ⟨y, rfl⟩; exact hv y⟩)
    (finHom V h) hu (hlat h).1
  let ψ : Dw.La ≃ₗ[𝓞 D.host.E] LinearMap.range io := LinearEquiv.ofInjective io hinj
  obtain ⟨k, γ, hγ1, hγ2, hγ3⟩ := GlobalTheory.selfDual_lattice_occurs hH _ H Dw l Xo σ' g ty F V.rank M (-D.host.xi0)
    (-V.gram.transpose) io (latG V h) (fun N => f N ∘ₗ ψ.toLinearMap) hA hσ hty hbase hW hφ hΛfg hΛsp hΛsd
    (fun N m hN hm a => hf2 N m hN hm (ψ a))
    (fun N hN => ⟨fun a => ((hf3 N hN).1 (ψ a)).trans
        ⟨fun ⟨v, hv⟩ => ⟨ψ.symm v, ψ.injective (by rw [hv, map_nsmul, LinearEquiv.apply_symm_apply])⟩,
          fun ⟨v, hv⟩ => ⟨ψ v, by rw [hv, map_nsmul]⟩⟩,
      fun a' => by
        obtain ⟨a, v, hv⟩ := (hf3 N hN).2 a'
        obtain ⟨a, rfl⟩ := ψ.surjective a
        exact ⟨a, v, hv⟩⟩)
    (fun N hN a a' => by
      obtain ⟨z, hz⟩ := hf4 N hN (ψ a) (ψ a')
      exact ⟨z, by rw [hφ.2.2.2.2]; exact hz⟩)
  obtain ⟨γ', hγ', hfin⟩ := genus_exists_rat D V γ hγ1
  have hmul : ∀ z, (finHom V (γ' * h)).1 *ᵥ z =
      γ.1.map (inclR (F := D.host.F) (Af D.host.F)) *ᵥ ((finHom V h).1 *ᵥ z) := fun z => by
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hfin]
  have hΛ : ∀ v, v ∈ (M.X k).Λ ↔ v ∈ AdLat.latOf D.host.F (finHom V (γ' * h)).1 (LinearMap.range io) := by
    intro v
    obtain ⟨v, rfl⟩ : ∃ u, γ.1 *ᵥ u = v :=
      ⟨(γ⁻¹).1 *ᵥ v, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
    rw [← hγ2, ← SetLike.mem_coe, (hlat h).1]
    refine exists_congr fun z => and_congr_right fun _ => ?_
    rw [hmul, genus_fv_mulVec, ← hfin]
    refine ⟨fun e => by rw [e], fun e => ?_⟩
    exact genus_mulVec_inj (finHom V γ') e
  refine ⟨⟨k, fun τ => (Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) (γ' * h)) * x₀ τ.1 :
    Matrix (Fin V.rank) (Fin V.rank) ℂ)⟩, γ', hγ', ?_, fun a ha => ?_, fun τ => rfl⟩
  · rw [(hlat _).1]
    refine Eq.trans ?_ (Set.image_id _).symm
    ext v
    exact hΛ v
  · obtain ⟨w, hw, e⟩ := hγ3 a ha
    obtain ⟨w', hw', e'⟩ := hf1 l.M (lt_of_lt_of_le (by norm_num) l.three_le) (ψ a)
    have m1 : AdLat.fv D.host.F w ∈ latGHat V (γ' * h) := by
      rw [← SetLike.mem_coe, (hlat _).2]
      exact (hΛ w).1 hw
    have m2 : (finHom V (γ' * h)).1 *ᵥ w' ∈ latGHat V (γ' * h) := by
      rw [← SetLike.mem_coe, (hlat _).2]
      exact ⟨w', hw', rfl⟩
    refine ⟨_, sub_mem m2 m1, ?_⟩
    change AdLat.fv D.host.F (M.φ k (F.t k a) : Fin V.rank → D.host.E) -
      (finHom V (γ' * h)).1 *ᵥ AdLat.fv D.host.F (io a) = _
    apply genus_sub_eq
    rw [← AdLat.Tower.mulVec_nsmul, ← Matrix.mulVec_add, hmul, ← AdLat.Tower.fv_nsmul, ← AdLat.Tower.fv_add, ← e,
      genus_fv_mulVec]
    exact congrArg _ e'.symm

theorem exists_markSpec : GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ h : GA D (D.sp.W j), ∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p :=
  fun hH D Q hQ j hj _ _ _ F hσ hty M io th x₀ hR h =>
    genus_marked hH D (D.sp.W j) F (level_good_and_sign D Q hQ).2.1 hσ hty (D.sp.W_rank j hj.1 hj.2) M io th x₀ hR h

end GlobalTheory.RecDict
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_markSpec_of_recOK : GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ h : GA D (D.sp.W j), ∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p := by
  atlas_forward_decl GlobalTheory.RecDict.exists_markSpec
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_uniform_embedding_third : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∀ (h h' : GA D (D.sp.W j)) (p : Σ k, Frame (M.X k).Ψ D.R.r) (γ' : GL (Fin D.R.r) D.host.E), γ' ∈ (M.X p.1).Γ → MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p → MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h' ⟨p.1, lact γ' p.2⟩ → ∃ γ ∈ GQ (D.sp.W j), ∃ k ∈ Kf, h' = γ * h * k := by
  first | exact @GlobalTheory.RecDict.double_coset_of_markSpec | exact GlobalTheory.RecDict.double_coset_of_markSpec | (intros; apply GlobalTheory.RecDict.double_coset_of_markSpec <;> assumption)
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkDict

theorem unitary_of_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (J : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix (Fin n) (Fin n) ℂ)
    (h : u.transpose * (-(Matrix.reindex e e J).transpose) * u.map (starRingEnd ℂ) =
      -(Matrix.reindex e e J).transpose) :
    ((Matrix.reindex e.symm e.symm u).map (starRingEnd ℂ)).transpose * J * Matrix.reindex e.symm e.symm u = J := by
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  have h' := congrArg (fun x => Matrix.reindex e.symm e.symm x.transpose) h
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.reindex_apply, Equiv.symm_symm,
    ← Matrix.submatrix_mul_equiv _ _ _ e _, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
    Matrix.submatrix_id_id] at h'
  rw [Matrix.mul_assoc]
  exact h'

theorem orth_mem_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : IsOrthogonalFrame X x₀) :
    (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) ∈ X.dom :=
  ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1
    (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) (fun τ => h τ.1 τ.2)).1

theorem archM_mul {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

theorem markSpec_mul_inf {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} {r : ℕ}
    (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hx : ∀ k, IsOrthogonalFrame (M.X k) x₀)
    (h h' : GA D V) (hh' : h' ∈ GinfC V) (p : Σ k, Frame (M.X k).Ψ r) (hp : MarkSpec M V hr io th x₀ h p) :
    MarkSpec M V hr io th x₀ (h * h')
      ⟨p.1, rmul p.2 (archMat V th hr (fun c (τ : (M.X c).Ψ) => (x₀ τ.1 : Fin r → Fin r → ℂ)) h' p.1)⟩ := by
  obtain ⟨γ, hγ, h1, h2, h3⟩ := hp
  have hf : finHom V (γ * (h * h')) = finHom V (γ * h) := by
    rw [← mul_assoc, map_mul (finHom V) (γ * h), (show finHom V h' = 1 from hh'), mul_one]
  have hg : gLat V (γ * (h * h')) = gLat V (γ * h) := by unfold gLat; rw [hf]
  have hl : latG V (γ * (h * h')) = latG V (γ * h) := by unfold latG; rw [hg]
  have hl' : latGHat V (γ * (h * h')) = latGHat V (γ * h) := by unfold latGHat; rw [hg]
  refine ⟨γ, hγ, ?_, ?_, fun τ => ?_⟩
  · rw [hl]; exact h1
  · rw [hl', hf]; exact h2
  · have hd : IsUnit (x₀ τ.1).det := isUnit_iff_ne_zero.2 (orth_mem_dom (M.X p.1) x₀ (hx p.1) τ).1
    show mat p.2 τ * ((x₀ τ.1)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) h') * x₀ τ.1) = _
    rw [h3 τ, ← mul_assoc γ, archM_mul V _ (γ * h) h']
    simp only [Matrix.reindex_apply, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr hr).symm _, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hd]

set_option maxHeartbeats 1000000 in

theorem dictIsUnif_of_markSpec : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∀ dict : GA D (D.sp.W j) → Σ k, Frame (M.X k).Ψ D.R.r, (∀ h, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h (dict h)) → (∀ h, (∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧ ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) → ∀ τ : (M.X (dict h).1).Ψ, mat (dict h).2 τ = x₀ τ.1) → DictIsUnif (D.sp.W j) dict Kf th (D.sp.W_rank j hj.1 hj.2) := by
  intro hT hL D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec Kf hK dict hd hpref
  have s1 := GlobalTheory.T.frame_uniform_embedding_second hT hL D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec Kf hK
  have s2 := GlobalTheory.T.frame_uniform_embedding_third D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec Kf hK
  have sc := GlobalTheory.RecDict.component_attained_at_base_frame D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec
  have su := GlobalTheory.MarkUnit.mark_frame_unit D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec
  obtain ⟨-, hW, -, -, hth, hx⟩ := hrec
  have s0 : ∀ h p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p →
      ∃ γ' ∈ (M.X p.1).Γ, dict h = ⟨p.1, lact γ' p.2⟩ := fun h p hp =>
    s1 h 1 1 p (dict h) (one_mem _) (one_mem _) hp (by rw [one_mul, mul_one]; exact hd h)
  refine ⟨fun γ hγ h => ?_, fun k hk h => ?_,
    ⟨fun c (τ : (M.X c).Ψ) => (x₀ τ.1 : Fin D.R.r → Fin D.R.r → ℂ), fun c => ⟨?_, ?_⟩, fun h h' hh' => ?_⟩,
    fun h => (su h _ (hd h)).1, fun c x hxd => ?_, ?_⟩
  · exact s1 h γ 1 _ _ hγ (one_mem _) (hd h) (by rw [mul_one]; exact hd _)
  · exact s1 h 1 k _ _ (one_mem _) hk (hd h) (by rw [one_mul]; exact hd _)
  · exact orth_mem_dom _ x₀ (hx c)
  · obtain ⟨h, -, p, rfl, hp0, hp⟩ := sc c
    have e := hpref h ⟨p, hp, hp0⟩
    obtain ⟨γ', -, e'⟩ := s0 h p hp
    refine ⟨h, ?_⟩
    rw [e'] at e ⊢
    exact congrArg (Sigma.mk p.1) (funext fun τ => e τ)
  · exact s0 _ _ (markSpec_mul_inf M _ _ io th x₀ hx h h' hh' _ (hd h))
  · obtain ⟨h, -, p, rfl, hp0, hp⟩ := sc c
    obtain ⟨a1, a2⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E D.R.r (M.X p.1).p0
      (M.X p.1).Ψ (M.X p.1).Gm (M.X p.1).Gm_herm
    obtain ⟨x₁, b, hb, hx₁, rfl⟩ := a1 x hxd
    choose u hu hux using fun τ : (M.X p.1).Ψ => a2 τ.1 (x₀ τ.1) (mat (rmul x b) τ) (hx p.1 τ.1 τ.2)
      ((hx₁ τ).trans (hx p.1 τ.1 τ.2).symm)
    have hG : ∀ τ : D.host.E →+* ℂ, (M.X p.1).Gm.map τ = -(Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2))
        (finCongr (D.sp.W_rank j hj.1 hj.2)) ((D.sp.W j).gram.map τ)).transpose := by
      intro τ
      rw [(hW p.1).1]
      ext a b
      simp
    obtain ⟨h', hh', hu'⟩ := ((GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.W j)).2 (M.X p.1).Ψ (th p.1) (M.X p.1).cmType
      (hth p.1)).2.2.2 (fun τ => Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2)).symm
        (finCongr (D.sp.W_rank j hj.1 hj.2)).symm (u τ))
      (fun τ => unitary_of_reindex _ _ _ (by rw [← hG]; exact hu τ))
    obtain ⟨γ', hγ', e'⟩ := s0 _ _ (markSpec_mul_inf M _ _ io th x₀ hx h h' hh' _ hp)
    refine ⟨h * h', γ', hγ', b, hb, e'.trans (congrArg (Sigma.mk p.1) (funext fun τ => ?_))⟩
    have hdet : IsUnit (x₀ τ.1).det := isUnit_iff_ne_zero.2 (orth_mem_dom (M.X p.1) x₀ (hx p.1) τ).1
    show (γ' : Matrix _ _ D.host.E).map τ.1 * (mat p.2 τ * ((x₀ τ.1)⁻¹ *
      Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2)) (finCongr (D.sp.W_rank j hj.1 hj.2))
        (archM (D.sp.W j) (th p.1 τ) h') * x₀ τ.1)) = ((γ' : Matrix _ _ D.host.E).map τ.1 * mat x τ) * mat b τ
    have hxb : mat x τ * mat b τ = u τ * x₀ τ.1 := hux τ
    rw [hp0 τ, hu' τ, ← Matrix.reindex_symm, Equiv.apply_symm_apply, Matrix.mul_assoc _ (mat x τ), hxb,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  · rintro h h' ⟨γ', hγ', e⟩
    exact s2 h h' (dict h) γ' hγ' (hd h) (by rw [← e]; exact hd h')

end GlobalTheory.MarkDict
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_uniform_embedding_fourth : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∀ dict : GA D (D.sp.W j) → Σ k, Frame (M.X k).Ψ D.R.r, (∀ h, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h (dict h)) → (∀ h, (∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧ ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) → ∀ τ : (M.X (dict h).1).Ψ, mat (dict h).2 τ = x₀ τ.1) → DictIsUnif (D.sp.W j) dict Kf th (D.sp.W_rank j hj.1 hj.2) := by
  atlas_forward_decl GlobalTheory.MarkDict.dictIsUnif_of_markSpec
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkLocal

theorem markSpec_arch {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} {r : ℕ}
    (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (g₀ : GA D V) (p : Σ k, Frame (M.X k).Ψ r)
    (hp : MarkSpec M V hr io th x₀ g₀ p) :
    ∃ γ : GA D V, ∀ k ∈ GfC V, ∀ h ∈ GinfC V, MarkSpec M V hr io th x₀ (g₀ * h)
      ⟨p.1, fun τ => (Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) (γ * (g₀ * k * h))) * x₀ τ.1 :
        Matrix (Fin r) (Fin r) ℂ)⟩ := by
  obtain ⟨γ, hγ, h1, h2, -⟩ := hp
  refine ⟨γ, fun k hk h hh => ?_⟩
  have hk' : infHom V k = 1 := hk
  have hh' : finHom V h = 1 := hh
  have ef : finHom V (γ * (g₀ * h)) = finHom V (γ * g₀) := by
    simp only [map_mul, hh', mul_one]
  have ei : infHom V (γ * (g₀ * k * h)) = infHom V (γ * (g₀ * h)) := by
    simp only [map_mul, hk', mul_one]
  have eg : gLat V (γ * (g₀ * h)) = gLat V (γ * g₀) := by
    unfold gLat
    rw [ef]
  have e1 : latG V (γ * (g₀ * h)) = latG V (γ * g₀) := by
    unfold latG
    rw [eg]
  have e2 : latGHat V (γ * (g₀ * h)) = latGHat V (γ * g₀) := by
    unfold latGHat
    rw [eg]
  refine ⟨γ, hγ, ?_, ?_, fun τ => ?_⟩
  · rw [e1]
    exact h1
  · rw [e2, ef]
    exact h2
  · unfold archM
    rw [← ei]
    rfl

set_option maxHeartbeats 1000000 in

theorem dict_locally_continuous : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ dict : GA D (D.sp.W j) → Σ k, Frame (M.X k).Ψ D.R.r, (∀ h, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h (dict h)) → (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (M.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (M.X k).dom ∧ ∃ γ ∈ (M.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) := by
  intro hT hL D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec dict hdict g₀
  obtain ⟨Kf, hK, -⟩ := GlobalTheory.RecDict.exists_isLevelK D (D.sp.W j) (D.host.g 0 * D.host.g 1)
  have hN := GlobalTheory.LevelOpen.level_mem_nhds D (D.sp.W j) _ Kf
    (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hK g₀
  obtain ⟨γ, hγ⟩ := markSpec_arch M _ _ io th x₀ g₀ _ (hdict g₀)
  have hc := ((GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.W j)).2 _ (th (dict g₀).1) (M.X (dict g₀).1).cmType
    (hrec.2.2.2.2.1 _)).2.2.1
  refine ⟨_, hN, (dict g₀).1, fun u τ => (Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2))
    (finCongr (D.sp.W_rank j hj.1 hj.2)) (archM _ (th (dict g₀).1 τ) (γ * u)) * x₀ τ.1 :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ), ?_, ?_⟩
  · haveI : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D (D.sp.W j)) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (D.sp.W j).gram))
    refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    exact (((hc τ).comp (continuous_const.mul continuous_id)).matrix_reindex _ _).matrix_mul continuous_const
  · rintro _ ⟨k, hk, h, hh, rfl⟩
    have hkf := ((hK k).1 hk).1
    have hs := hγ k hkf h hh
    refine ⟨(GlobalTheory.MarkUnit.mark_frame_unit D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec _ _ hs).1, ?_⟩
    have e : g₀ * k * h = 1 * (g₀ * h) * k := by
      rw [one_mul, mul_assoc, mul_assoc, (GlobalTheory.UnitarySplit.real_finite_split D _).2.1 h hh k hkf]
    exact GlobalTheory.T.frame_uniform_embedding_second hT hL D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec Kf hK (g₀ * h) 1 k _ _ (one_mem _) hk hs
      (e ▸ hdict (g₀ * k * h))

end GlobalTheory.MarkLocal
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_uniform_embedding_fifth : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ dict : GA D (D.sp.W j) → Σ k, Frame (M.X k).Ψ D.R.r, (∀ h, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h (dict h)) → (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (M.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (M.X k).dom ∧ ∃ γ ∈ (M.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) := by
  atlas_forward_decl GlobalTheory.MarkLocal.dict_locally_continuous
end

section
section
noncomputable section

namespace GlobalTheory.RecPkg

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

set_option maxHeartbeats 1000000 in

theorem exists_package : PartI → N1ab → N1c → ThetaUnifAV → Out.Laws → Out.Laws2 → GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ (j : ℕ) (hj : InR D j) (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ → ∀ io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E), LatEmb (D.sp.W j) io → (∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) (io y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm))) → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W j) dict Kf th (D.sp.W_rank j hj.1 hj.2) ∧ (∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (U.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) ∧ (∀ k, ModelW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (U.X k) ∧ IsOrthogonalFrame (U.X k) x₀) ∧ FJ.LatZ U.X (WeightFamilies.rho D j) ∧ FJ.CuNeF U.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ), DictLat U (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) dict io e F ik φ th x₀ := by
  intro _ _ hN hTh hL hL2 hH D Q hQ hpq j hj σ hσ io hio hEF Kf hKf
  classical
  let g := Fintype.card (Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ))
  let e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ) := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good _ Q.H Q.l Q.c σ hσ).2.2.2 (Q.Dw j) g e
  have hρ : (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (baseKA Q.l).ρ = Q.H.rt0 := hσ
  obtain ⟨F⟩ := hN _ Q.H (Q.Dw j) Q.l (Q.Xo j) _ g _ (hpq j) hρ hty
  obtain ⟨M, -, th, x₀, -, hneg, hall⟩ := GlobalTheory.RecModel.exists_recOK hH D Q hQ j hj _ g _ F hρ hty
  have hR := hall io hio hEF
  obtain ⟨un, hun⟩ := GlobalTheory.FrameUnif.exists_framesOK hL.secBaseChange hL2.secTwist _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ g e
    F _ M hσ hR.1 hneg
  have hU := GlobalTheory.FrameUnif.isUnf_built hL.secBaseChange _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c σ g e F _ M un hσ hR.1 hneg hun
  have hG := GlobalTheory.T.exists_markSpec_of_recOK hH D Q hQ j hj _ g _ F hρ hty M io th x₀ hR
  have hex : ∀ h : GA D (D.sp.W j), ∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧
      ((∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧
        ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) → ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) := by
    intro h
    by_cases h' : ∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧
        ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1
    · obtain ⟨p, hp, hp'⟩ := h'
      exact ⟨p, hp, fun _ => hp'⟩
    · obtain ⟨p, hp⟩ := hG h
      exact ⟨p, hp, fun h'' => (h' h'').elim⟩
  choose dict hd hb using hex
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.RecDict.lat_cusp_expo hH D Q hQ j hj _ g _ F hρ hty M io th x₀ hR
  refine ⟨(GlobalTheory.FrameUnif.unfOf e F M un).toPj, dict, x₀, th, hU, hR.1.chi, hR.2.2.2.2.1,
    GlobalTheory.T.frame_uniform_embedding_fourth hTh hL D Q hQ j hj _ g _ F hρ hty M io th x₀ hR Kf hKf dict hd hb,
    fun h => (GlobalTheory.MarkUnit.mark_frame_unit D Q hQ j hj _ g _ F hρ hty M io th x₀ hR h _ (hd h)).2,
    GlobalTheory.T.frame_uniform_embedding_fifth hTh hL D Q hQ j hj _ g _ F hρ hty M io th x₀ hR dict hd,
    fun k => ⟨hR.2.1 k, hR.2.2.2.2.2 k⟩, c1, c2, c3, g, e, F, id, M.φ, ⟨hR.1.ef, fun k x => ?_⟩, hd⟩
  obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun.1 k x
  exact ⟨Pm, h1, h2, h3, h4⟩

end GlobalTheory.RecPkg
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_embedding_trace_form : PartI → N1ab → N1c → ThetaUnifAV → Out.Laws → Out.Laws2 → GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ (j : ℕ) (hj : InR D j) (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ → ∀ io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E), LatEmb (D.sp.W j) io → (∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) (io y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm))) → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W j) dict Kf th (D.sp.W_rank j hj.1 hj.2) ∧ (∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (U.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) ∧ (∀ k, ModelW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (U.X k) ∧ IsOrthogonalFrame (U.X k) x₀) ∧ FJ.LatZ U.X (WeightFamilies.rho D j) ∧ FJ.CuNeF U.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ), DictLat U (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) dict io e F ik φ th x₀ := by
  atlas_forward_decl GlobalTheory.RecPkg.exists_package
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory

theorem exists_unf_nonempty_frame : N1c → Out.SecTwistSt → ∀ (D : D7) (Q : Par D), (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → Nonempty (Data D.host.E D.R.r) → ∀ j (σ : Q.c.F →+* ℂ), ∃ U : Unf (Q.Xo j) Q.c σ D.R.r, Nonempty (Σ k, Frame (U.X k).Ψ D.R.r) := by
  intro hN hT D Q h hX j σ
  obtain ⟨X⟩ := hX
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex hN hT _ _ (Q.Dw j) _ (Q.Xo j) Q.c (h j) σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨⟨(), fun _ => 0⟩⟩⟩

end GlobalTheory
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.ExtCore

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, sq_emb, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  rw [h.2 _ _ (isDetRoot_mul V g g' x x' hx hx'), h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem exists_latEmb (D : D7) (Q : Par D) (hQ : Q.Pins) (j : ℕ) :
    ∃ ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), ∀ hj : InR D j,
      let io := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι₀
      LatEmb (D.sp.W j) io ∧ LatIsom (D.sp.W j) (Q.Dw j).EF io ∧
        ∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
          herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm)
            (io y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm)) := by
  by_cases hj : InR D j
  · obtain ⟨io, h1, h2, -, -, -, h3⟩ := GlobalTheory.RecDict.exists_latEmb_sign_one D Q hQ j hj
    refine ⟨LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ io, fun hj' => ?_⟩
    have he : LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj'.1 hj'.2)) ∘ₗ
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ io) = io := by
      ext x i
      rfl
    intro io'
    have : io' = io := he
    rw [this]
    exact ⟨h1, h2, h3⟩
  · exact ⟨0, fun h => absurd h hj⟩

set_option maxHeartbeats 1000000 in

theorem exists_coreJ : PartI → N1ab → N1c → ThetaUnifAV → Out.Laws → Out.Laws2 → GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → VolTieG D → ∀ (chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle) (mu : ∀ j, (Q.c.F →+* ℂ) → GA D (D.sp.W j) → ℂ), (∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuVal (D.sp.W j) (chiW j σ) (mu j σ) ∧ (∀ γ ∈ GQ (D.sp.W j), mu j σ γ = 1) ∧ Continuous (mu j σ) ∧ MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.Q = Q ∧ HEq T.chiW chiW := by
  intro hI hA hC hTh hL hL2 hH D Q hQ hpq hV chiW mu hmu
  have hB := hL.secBaseChange
  have hT := hL2.secTwist
  have h0 : GoodEmb Q.c Q.c.F.val.toRingHom := rfl
  have h1 : InR D 1 := ⟨le_rfl, by have := D.R.two_le_m; omega⟩
  obtain ⟨hgood, -, -⟩ := GlobalTheory.RecDict.level_good_and_sign D Q hQ
  obtain ⟨pb, hpb⟩ := GlobalTheory.LevelHalf.half_eq_prod D Q hQ
  choose ι hι using exists_latEmb D Q hQ
  choose Kf hKf _hKf' using fun j => GlobalTheory.RecDict.exists_isLevelK D (D.sp.W j) (D.host.g 0 * D.host.g 1)
  have hpk := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.T.lattice_embedding_trace_form hI hA hC hTh hL hL2 hH D Q hQ hpq j hj σ hσ _ (hι j hj).1 (hι j hj).2.2 (Kf j) (hKf j)
  have hne : Nonempty (Data D.host.E D.R.r) := by
    obtain ⟨U, dict, -⟩ := hpk 1 h1 _ h0
    exact ⟨U.X (dict 1).1⟩
  have hall : ∀ j (σ : Q.c.F →+* ℂ), ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r)
      (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r)
      (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), ∀ hj : InR D j, GoodEmb Q.c σ →
      ∃ th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W j) dict (Kf j) th (D.sp.W_rank j hj.1 hj.2) ∧ (∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (U.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) ∧ (∀ k, ModelW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (U.X k) ∧ IsOrthogonalFrame (U.X k) x₀) ∧ FJ.LatZ U.X (WeightFamilies.rho D j) ∧ FJ.CuNeF U.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ), DictLat U (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι j) e F ik φ th x₀ := by
    intro j σ
    by_cases h : InR D j ∧ GoodEmb Q.c σ
    · obtain ⟨U, dict, x₀, h'⟩ := hpk j h.1 σ h.2
      exact ⟨U, dict, x₀, fun _ _ => h'⟩
    · obtain ⟨U, ⟨p⟩⟩ := GlobalTheory.exists_unf_nonempty_frame hC hT D Q hpq hne j σ
      exact ⟨U, fun _ => p, fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩
  choose U dict x₀ th hunf hchi hth hdict hunit hloc hmod hlatZ hcu hexpo hpin using hall
  have hmuU : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuUnit (D.sp.W j) (dict j σ) (mu j σ) := fun j hj σ hσ =>
    ⟨muVal_mul (hmu j hj σ hσ).1, (hmu j hj σ hσ).1.norm, (hmu j hj σ hσ).2.1, hunit j σ hj hσ⟩
  have hsup : ∀ j, InR D j → SupDef (Q.Xo j) Q.c (U j) := fun j hj =>
    supDef_of _ _ _ fun a n _ σ hσ f hf hz =>
      (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (Q.Xo j) Q.c σ _
        (Formalism.L2.PjFree.Unf.ofPj (U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hunf j σ hj hσ)) a n).2 f
        ((mem_cusp _ _ _ _ _ _).1 hf).1 hz
  have hsq := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.CuspSqInt.cusp_l2_and_definite D _ _ _ (Q.Xo j) Q.c _ (U j) σ (D.sp.W j) (dict j σ) (mu j σ) (Kf j)
      (th j σ hj hσ) _ hV (D.sp.W_sig j) hσ (hchi j σ hj hσ) (hdict j σ hj hσ) (hmuU j hj σ hσ)
      (hmu j hj σ hσ).2.2.1 (hloc j σ hj hσ) (hsup j hj)
  have halg := fun j => GlobalTheory.Frames.algebraic_laws hB _ _ _ _ (Q.Xo j) Q.c
  let T : CoreJ D :=
    { Q := Q, U := U, V := fun j _ => D.sp.W j, dict := dict, mu := mu, Kf := fun j _ => Kf j, pb := pb,
      cE := fun _ _ _ => 1, chiW := chiW, x₀ := x₀, iota := ι }
  have hM : LawsM T.toCore :=
    { pins := hQ
      half := hpb
      evalWD := fun j _ => (halg j).2.2.1
      unf := fun j hj σ hσ => hunf j σ hj hσ
      unTest := fun j _ σ _ k x =>
        haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
        GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ (Q.Xo j) Q.c (CAt σ) ((U j σ).un k x)
      chiTriv := fun j hj σ hσ _ _ _ k γ _ => hchi j σ hj hσ k _ γ
      dictU := fun j hj σ hσ => ⟨th j σ hj hσ, _, hth j σ hj hσ, hdict j σ hj hσ⟩
      spaceW := fun _ _ _ _ => rfl
      levelK := fun j _ _ _ => hKf j
      xiAbs := fun j hj σ hσ k τ =>
        (congrArg (fun z => ‖τ z‖) (hmod j σ hj hσ k).1.2).trans (by rw [map_neg, norm_neg]; exact norm_embedding_hostFormConstant_eq D τ)
      muUnit := hmuU
      muCont := fun j hj σ hσ => (hmu j hj σ hσ).2.2.1
      finVol := fun j _ _ _ => finVol_alt hV j
      cuspFD := fun j hj => (Formalism.L2.PjFree.cuspFD_ofPj (U j)).1
        (GlobalTheory.cuspForms_finiteDimensional_of_isUnf hB _ _ _ _ (Q.Xo j) Q.c _
          (fun σ => Formalism.L2.PjFree.Unf.ofPj (U j σ)) _ h0 ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hunf j _ hj h0)))
      supDef := hsup
      cuspidalL2Subspace := fun j hj σ hσ => (hsq j hj σ hσ).choose
      l2Def := fun j hj σ hσ => (hsq j hj σ hσ).choose_spec
      unitIndep := fun j _ => (halg j).2.2.2.2.2.1
      ptNe := fun j _ =>
        GlobalTheory.integralAlgebraicFramedPoint_exists hI hA hC hB hT _ _ _ _ (Q.Xo j) Q.c (hpq j) hgood }
  refine ⟨T, ?_, ?_, rfl, HEq.rfl⟩
  · exact
      { toLawsM := hM
        cUnit := fun _ _ _ _ _ => norm_one
        muVal := fun j hj σ hσ => (hmu j hj σ hσ).1
        muConj := fun j hj σ hσ => (hmu j hj σ hσ).2.2.2
        intAll := fun j _ => GlobalTheory.IntegralFrames.intAll hI hA hB hT _ _ _ _ (Q.Xo j) Q.c (hpq j) hgood
        modelW := fun j hj σ hσ => ⟨_, fun k => (hmod j σ hj hσ k).1⟩
        familyUniformisationBasePointOrthogonal := fun j hj σ hσ k => (hmod j σ hj hσ k).2
        kfHalf := fun j _ _ _ => GlobalTheory.LevelHalf.kfHalf_record D Q hQ j (Kf j) (hKf j)
        adPin := fun j hj σ hσ => by
          obtain ⟨g, e, F, ik, φ, h⟩ := hpin j σ hj hσ
          exact ⟨D.sp.W_rank j hj.1 hj.2, g, e, F, ik, φ, th j σ hj hσ, (hι j hj).1, (hι j hj).2.1,
            hth j σ hj hσ, h⟩ }
  · exact
      { toLawsM := hM
        cuspMul := fun j _ => cusp_mul_of_M5 siegelSpaceAlgebra_holds (U j)
        latZ := fun j hj => hlatZ j _ hj h0
        cuNe := fun j hj => hcu j _ hj h0
        expo := fun j hj => hexpo j _ hj h0 }

end GlobalTheory.ExtCore
end
