module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.jacquet_quotient_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ (μ : ℂ) (w : V), (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 → (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) : Jacquet π (unipRad k (stdBlocks d hd))) = μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) → ∃ (x : Fin 2 → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧ Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧ ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 := by
  first | exact @GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen | exact GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen | (intros; apply GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen <;> assumption)
