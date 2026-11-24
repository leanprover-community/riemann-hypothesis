module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightPolynomialTraceIdentity
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

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope

theorem _root_.GlobalTheory.T.weight_polynomial_trace_identity : ∀ {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    (⨆ μ, wtDual E μ) = ⊤ → iSupIndep (wtDual E) → ∀ s : Finset (Fin n → ℤ), (∀ μ, wtDual E μ ≠ ⊥ → μ ∈ s) →
      cPoly s (fun μ => trOn (wtDual E μ) (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * altL (delZ n) ^ 2 =
          pPL n * altL (lam + delZ n) ^ 2 ∧
        cPoly s (fun μ => trOn (wtDual E μ) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * frL n (altL (delZ n)) =
          pPL n * frL n (altL (lam + delZ n)) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident | exact GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident | (intros; apply GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident <;> assumption)
