module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
public import Mathlib.Algebra.BigOperators.Fin
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capelli :
    ∀ (A : Type) [Ring A] (X D a : Fin 2 → Fin 2 → A) (q Δ h : A), (∀ i j k l, X i j * X k l = X k l * X i j) → (∀ i j k l, D i j * D k l = D k l * D i j) →
    (∀ i j k l, D i j * X k l = X k l * D i j + if i = k ∧ j = l then 1 else 0) →
    (∀ i j, a i j = -(if i = j then 1 else 0) - ∑ b, X j b * D i b) → q = X 0 1 * X 1 0 - X 0 0 * X 1 1 → Δ = D 0 1 * D 1 0 - D 0 0 * D 1 1 →
    h = (∑ i, ∑ j, X i j * D i j) + 2 →
    Δ * q - q * Δ = h ∧ a 0 0 + a 1 1 = -h ∧
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h - 2 * (q * Δ + Δ * q) := by
  intro A _ X D a q Δ h hX hD hDX ha hq hΔ hh
  have hDX' : ∀ i j k l z, D i j * (X k l * z) = X k l * (D i j * z) + if i = k ∧ j = l then z else 0 := by
    intro i j k l z
    rw [← mul_assoc, hDX, add_mul, mul_assoc]
    split_ifs <;> simp
  have hX' : ∀ i j k l z, X i j * (X k l * z) = X k l * (X i j * z) := by
    intro i j k l z
    rw [← mul_assoc, hX, mul_assoc]
  have h2 : (2 : A) = 1 + 1 := by norm_num
  have h01 : ¬ ((0 : Fin 2) = 1) := by decide
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  subst hq hΔ hh
  simp only [ha, Fin.sum_univ_two, h2, h01, h10, if_true, if_false]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    try simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_zero, zero_sub, neg_neg, mul_one, one_mul, mul_assoc, hDX, hDX', h01, h10, and_self, and_true, true_and, and_false, false_and, if_true, if_false, add_zero,
      hX 1 1 0 0, hX 1 1 0 1, hX 1 1 1 0, hX 1 0 0 0, hX 1 0 0 1, hX 0 1 0 0,
      hX' 1 1 0 0, hX' 1 1 0 1, hX' 1 1 1 0, hX' 1 0 0 0, hX' 1 0 0 1, hX' 0 1 0 0,
      hD 1 1 0 0, hD 1 1 0 1, hD 1 1 1 0, hD 1 0 0 0, hD 1 0 0 1, hD 0 1 0 0]
  all_goals abel
