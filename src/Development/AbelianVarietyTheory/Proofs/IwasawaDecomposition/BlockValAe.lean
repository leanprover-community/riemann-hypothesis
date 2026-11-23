module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiser
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.BlockVal

open NumberField IsDedekindDomain Polynomial in
private theorem block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv {E : Type} [Field E] [NumberField E]
    (μ η : _root_.Formalism.L2.Host.HChar E) (r : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ)) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) := by
  have hval : (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) :=
    _root_.GlobalTheory.GalChar.block_val μ η r v
  have hN : (_root_.Formalism.ConjugateSelfDual.normV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    unfold _root_.Formalism.ConjugateSelfDual.normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := _root_.GlobalTheory.GalChar.absNorm_ne_zero v
    exact_mod_cast this
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne)
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNdef
  have hpow : (N : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N ^ r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hpos.le]
    congr 2
    ring
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [hval, hN]
  have hcast : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (N : ℂ) := by simp [hNdef]
  rw [hcast, hpow, zpow_neg, zpow_natCast, Complex.ofReal_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hs)), mul_one]


open NumberField IsDedekindDomain Polynomial in
theorem _root_.GlobalTheory.BlockVal.block_val_ae : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ)
    (μ η : _root_.Formalism.L2.Host.HChar E),
    _root_.GlobalTheory.GalChar.AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r →
    ∀ (μH ηH : _root_.Formalism.L2.NC.HC E),
    μH.χ = (μ : _root_.Neutral.B1.Ideles E →* ℂˣ) → ηH.χ = (η : _root_.Neutral.B1.Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite,
    (μH * ηH⁻¹).At v ((((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) *
      (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ))) ∧
    ∃ y : K, ε y = (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  intro E _ _ K _ ε μ η hμ hη r hr μH ηH hμH hηH
  have hχ : (μH * ηH⁻¹).χ = ((μ * η⁻¹ : _root_.Formalism.L2.Host.HChar E) : _root_.Neutral.B1.Ideles E →* ℂˣ) := by
    change μH.χ * ηH.χ⁻¹ = _
    rw [hμH, hηH]
    rfl
  have hblock := _root_.GlobalTheory.GalChar.AlmostIn.block hμ hη hr
  unfold _root_.GlobalTheory.GalChar.AlmostIn at hblock
  filter_upwards [hblock, _root_.GlobalTheory.GalChar.unr_ae (μ * η⁻¹)] with v hv hunr
  refine ⟨?_, ?_⟩
  · rw [block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv]
    exact (_root_.GlobalTheory.HeckeUnifVal.at_val_and_unr_iff (μ * η⁻¹) (μH * ηH⁻¹) hχ v).1 hunr
  · obtain ⟨y, hy⟩ := hv
    exact ⟨y⁻¹, by rw [map_inv₀, hy]⟩

end GlobalTheory.BlockVal
