module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.FockMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatSurj
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.exPhi :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (a : (A F)ˣ), ∀ k ∈ KK F, ∃ φ ∈ Fock D.δ, hat (W.Om (mD a * k) φ).1 ![0, 1, 1, 0] ≠ 0 := by
  intro F E _ _ _ _ _ _ _ D W a k hk
  have H := hatSt F E D W
  have K := fockSt F E D W
  obtain ⟨χ, hχ, hne⟩ := (fockMul F D.δ).2 ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]
  obtain ⟨φ₁, hφ₁, hh⟩ := hatSurj F D.δ D.neg χ hχ
  have hk' : k⁻¹ ∈ KK F := by
    have hs := (M.kkCpt F).1
    rw [hs] at hk ⊢
    exact inv_mem hk
  obtain ⟨U, hU, -, hC⟩ := K.om φ₁ hφ₁ {k⁻¹} isCompact_singleton (by rintro _ rfl; exact hk'.1)
  refine ⟨W.Om k⁻¹ φ₁, hU (hC _ rfl), ?_⟩
  have e : W.Om (mD a * k) (W.Om k⁻¹ φ₁) = W.Om (mD a) φ₁ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
  have hv : (![a * (![0, 1, 1, 0] : V4 F) 0, ((a⁻¹ : (A F)ˣ) : A F) * (![0, 1, 1, 0] : V4 F) 1,
      a * (![0, 1, 1, 0] : V4 F) 2, a * (![0, 1, 1, 0] : V4 F) 3] : V4 F) =
      ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
    ext1 i
    fin_cases i <;> simp
  rw [e, H.m, hh, hv]
  have hab : ((ab a : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ab a := (IdeleGroup.ideleModule F a).2
    exact_mod_cast this.ne'
  exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) hab) hne
