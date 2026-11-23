module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def UpperTheory.V.Ws.P1.formJ (R : Type) [CommRing R] : M4 R :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private theorem UpperTheory.V.Ws.P1.formJ_sq (R : Type) [CommRing R] :
    UpperTheory.V.Ws.P1.formJ R * UpperTheory.V.Ws.P1.formJ R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.P1.formJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem UpperTheory.V.Ws.P1.formJ_adj (R : Type) [CommRing R] (g : M4 R) :
    g.transpose * UpperTheory.V.Ws.P1.formJ R = UpperTheory.V.Ws.P1.formJ R * UpperTheory.V.GradeZeroInterpolatingElement.adj g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.V.Ws.P1.formJ, Matrix.mul_apply, Fin.sum_univ_four, UpperTheory.V.GradeZeroInterpolatingElement.adj, UpperTheory.V.GradeZeroInterpolatingElement.sgn, Fin.rev]

theorem UpperTheory.V.Ws.P1.gspForm :
    ∀ (R : Type) [CommRing R], ∃ J : (M4 R)ˣ, (J : M4 R).transpose = -J ∧ ∀ (ν : R) (g : M4 R), IsGSp ν g → g.transpose * (J : M4 R) * g = ν • (J : M4 R) := by
  intro R _
  refine ⟨⟨UpperTheory.V.Ws.P1.formJ R, -UpperTheory.V.Ws.P1.formJ R, ?_, ?_⟩, ?_, ?_⟩
  · rw [mul_neg, UpperTheory.V.Ws.P1.formJ_sq, neg_neg]
  · rw [neg_mul, UpperTheory.V.Ws.P1.formJ_sq, neg_neg]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.P1.formJ]
  · intro ν g hg
    have h : UpperTheory.V.GradeZeroInterpolatingElement.adj g * g = ν • 1 := hg
    simp only [Units.val_mk]
    rw [UpperTheory.V.Ws.P1.formJ_adj, mul_assoc, h, Matrix.mul_smul, Matrix.mul_one]
