module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInnerPolynomialMovingGaussian
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hasDerivAt_inner_polynomial_moving_gaussian : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : ℝ → Matrix (Fin P) (Fin Q) ℂ) (x : ℝ → Ix P Q → ℂ) (v : ℝ → F.H) (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ), (∀ t, HasCoeff F (v t) (expPS (gaussPoly (A t) (x t)))) → (∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) → (∀ l, HasDerivAt (fun t => x t l) (x' l) 0) → ∀ f : MvPolynomial (Ix P Q) ℂ, HasDerivAt (fun t => inner ℂ (F.ι f) (v t)) (∑ i, ∑ j, A' i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) (v 0) + ∑ l, x' l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) (v 0)) 0 := by
  first | exact @GlobalTheory.OscPairDer.hasDerivAt_inner_gauss | exact GlobalTheory.OscPairDer.hasDerivAt_inner_gauss | (intros; apply GlobalTheory.OscPairDer.hasDerivAt_inner_gauss <;> assumption)
