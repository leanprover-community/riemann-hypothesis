module

public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjCoefficientsWeylModuleRowActNormFock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.conj_coefficients_weylModule_rowAct_normFock : ∀ (n : ℕ) (lam : DomWeight n), (∀ p ∈ delSq ℂ n lam, MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ), MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) = Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p)) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) ℂ, normFock lam (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) = normFock lam q p := by
  first | exact @GlobalTheory.ConjCoeff.conj_coefficients | exact GlobalTheory.ConjCoeff.conj_coefficients | (intros; apply GlobalTheory.ConjCoeff.conj_coefficients <;> assumption)
