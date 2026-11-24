module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

open scoped Pointwise

namespace GlobalTheory.SnMass.SkewDom

theorem im_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w : InfinitePlace E) (z : E) :
    (w.embedding (σ z)).im = -(w.embedding z).im := by
  rw [h.2.2.2 w.embedding z]; simp

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem mem_skewLat_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ x ∈ I, σ x ∈ I)
    {θ : 𝓞 E} (hθ : (θ : E) + σ θ = 1) (c : ℝ) (z : InfinitePlace E → ℝ) :
    z ∈ (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) ↔
      ∃ b ∈ {b | ∃ x ∈ I, imV x = b}, z = (2 * c) • b := by
  change (∃ y ∈ I, (σ : E →+* E) y = -y ∧ ∀ w, z w = c * (w.embedding y).im) ↔ _
  simp only [AlgHom.coe_toRingHom]
  constructor
  · rintro ⟨y, hy, hs, hz⟩
    have hθy : (θ : E) * y ∈ I := by
      have := (I : Submodule (𝓞 E) E).smul_mem θ hy
      rwa [Algebra.smul_def] at this
    refine ⟨imV ((θ : E) * y), ⟨(θ : E) * y, hθy, rfl⟩, ?_⟩
    funext w
    have hy2 : y = (θ : E) * y - σ ((θ : E) * y) := by
      rw [map_mul, hs]; linear_combination (-y) * hθ
    rw [hz w, Pi.smul_apply, smul_eq_mul, imV]
    conv_lhs => rw [hy2]
    rw [map_sub, Complex.sub_im, im_sigma hcm]; ring
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x - σ x, (I : Submodule (𝓞 E) E).sub_mem hx (hI x hx), ?_, fun w => ?_⟩
    · rw [map_sub, sigma_sigma hcm]; ring
    · rw [Pi.smul_apply, smul_eq_mul, imV, map_sub, Complex.sub_im, im_sigma hcm]; ring

theorem skewDom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  intro F E _ _ _ _ _ σ hcm I hI θ hθ c hc D m hD hU hm
  have hmem := mem_skewLat_iff hcm hI hθ c
  have h2c : (2 * c) ≠ 0 := by positivity
  refine ⟨(2 * c) • D, hD.const_smul₀ _, fun v => ?_, ?_⟩
  · obtain ⟨l, ⟨hl, hlD⟩, hu⟩ := hU ((2 * c)⁻¹ • v)
    refine ⟨(2 * c) • l, ⟨(hmem _).2 ⟨l, hl, rfl⟩, ?_⟩, ?_⟩
    · refine Set.mem_smul_set.2 ⟨_, hlD, ?_⟩
      rw [smul_add, smul_inv_smul₀ h2c]
    · rintro l' ⟨hl', hl'D⟩
      obtain ⟨b, hb, rfl⟩ := (hmem _).1 hl'
      obtain ⟨d, hd, hdv⟩ := Set.mem_smul_set.1 hl'D
      have hbd : (2 * c)⁻¹ • v + b = d := by
        rw [← inv_smul_smul₀ h2c d, hdv, smul_add, inv_smul_smul₀ h2c]
      rw [hu b ⟨hb, hbd ▸ hd⟩]
  · rw [Measure.addHaar_smul, hm, Module.finrank_fintype_fun_eq_card, abs_of_pos (by positivity)]

end GlobalTheory.SnMass.SkewDom
