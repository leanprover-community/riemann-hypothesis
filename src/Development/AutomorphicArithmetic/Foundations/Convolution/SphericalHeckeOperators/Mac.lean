module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
public import GroundTheory.AutomorphicForms.MacdonaldNormalization
public import GroundTheory.AutomorphicForms.MacdonaldSpherical
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoVol
public import GroundTheory.AutomorphicForms.MacdonaldFormula
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

theorem UpperTheory.ConvolutionTheory.H.mac :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (z : Fin n → ℂˣ) (a : Fin n → ℤ), Antitone a →
      vPoly n ((qF F : ℂ))⁻¹ * ∫ g, th μ a g * zonalSpherical μ z g ∂μ = evalAt z (hlR ((qF F : ℂ))⁻¹ a) := by
  intro F _ _ _ _ n _ _ μ _ z a ha
  have hm : MeasurableSet (dco F a) := by
    have h := ((dcoShape F n a ha).2.2.1.1.isOpen_fiber 1).measurableSet
    convert h using 1
    ext g
    by_cases hg : g ∈ dco F a <;> simp [uFn, hg]
  have hI : (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (HeckeAlgebra.measureReal_compactOpen_pos μ (isCompact_iwahori F n) (isOpen_iwahori F n)).ne'
  have e : (fun g => th μ a g * zonalSpherical μ z g) = (dco F a).indicator fun _ =>
      halfModulus F a / (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) * zonalSpherical μ z (torusPow F n a) := by
    funext g
    by_cases hg : g ∈ dco F a
    · rw [Set.indicator_of_mem hg, th, Pi.smul_apply, uFn, Set.indicator_of_mem hg]
      obtain ⟨x, hx, y, hy, rfl⟩ := hg
      rw [zonalSpherical_mul_right z _ (iwahori_le_integralGL F n hy),
        zonalSpherical_mul_left z (iwahori_le_integralGL F n hx)]
      simp
    · simp [th, uFn, hg]
  rw [e, integral_indicator_const _ hm, Complex.real_smul]
  have h1 := macdonald_formula_hlR (μ := μ) z ha
  have h2 := dcoVol F n μ a ha
  apply mul_right_cancel₀ hI
  calc _ = (μ.real (dco F a) : ℂ) * halfModulus F a *
        (vPoly n ((qF F : ℂ))⁻¹ * zonalSpherical μ z (torusPow F n a)) := by field_simp
    _ = _ := by rw [h1, ← h2]; ring
