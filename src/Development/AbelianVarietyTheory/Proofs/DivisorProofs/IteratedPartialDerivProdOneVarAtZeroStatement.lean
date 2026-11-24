module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedPartialDerivProdOneVarAtZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.iteratedPartialDeriv_prod_oneVar_at_zero : ∀ (I : Type) [Fintype I] [DecidableEq I] (u : List I) (r : ℝ) (ψ : I → ℂ → ℂ) (A : ℂ), 0 < r → (∀ i, DifferentiableOn ℂ (ψ i) (Metric.ball 0 r)) → iterD u (fun z ↦ A * ∏ i, ψ i (z i)) 0 = A * ∏ i, iteratedDeriv (u.count i) (ψ i) 0 := by
  first | exact @GlobalTheory.IterDProd.iterD_prod | exact GlobalTheory.IterDProd.iterD_prod | (intros; apply GlobalTheory.IterDProd.iterD_prod <;> assumption)
