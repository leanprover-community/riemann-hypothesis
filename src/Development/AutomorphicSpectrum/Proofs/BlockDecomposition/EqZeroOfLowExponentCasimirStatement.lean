module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimir
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

@[expose] public section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

theorem _root_.GlobalTheory.T.eq_zero_of_low_exponent_casimir : ∀ {n : ℕ} (m : Fin n × Fin n →₀ ℕ), LowExp m → (∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ)) → casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n) → m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | exact GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq <;> assumption)
