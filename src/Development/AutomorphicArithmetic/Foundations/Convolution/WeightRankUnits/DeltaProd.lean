module

public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.AbsProd
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MuProd
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.Regroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.deltaProd :
    UpperTheory.ConvolutionTheory.G2.DeltaProd := by
  intro E _ _ _ hE μ e hμ S hS a b P₁ P₂ h₁ h₂ hc
  have hR : resultant P₁ P₂ ≠ 0 := Polynomial.resultant_ne_zero P₁ P₂ hc
  obtain ⟨fm, hm⟩ := UpperTheory.ConvolutionTheory.G2.muProd E μ e hμ _ hR
  obtain ⟨fa, ha⟩ := UpperTheory.ConvolutionTheory.G2.absProd E _ hR
  have fg := (fm.union fa).subset (Function.mulSupport_mul
    (fun u : Pl E => UpperTheory.ConvolutionTheory.G2.muAt μ u (resultant P₁ P₂))
    (fun u : Pl E => absHalf u (algebraMap E (u.adicCompletion E) (resultant P₁ P₂))))
  obtain ⟨fG, hG⟩ := UpperTheory.ConvolutionTheory.G2.regroup E S hS _ fg
  have hd := UpperTheory.ConvolutionTheory.G2.deltaLoc E hE μ e hμ a b P₁ P₂ h₁ h₂ hc
  simp only [hd]
  refine ⟨fG, ?_⟩
  rw [hG, finprod_mul_distrib fm fa]
  simp only [UpperTheory.ConvolutionTheory.G2.phase]
  rw [Finset.prod_mul_distrib, mul_mul_mul_comm, hm, ha, one_mul]
