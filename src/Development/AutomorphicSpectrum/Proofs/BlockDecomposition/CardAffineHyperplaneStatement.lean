module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardAffineHyperplane
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf

@[expose] public section

open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

theorem _root_.GlobalTheory.T.card_affine_hyperplane : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one | exact GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one | (intros; apply GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one <;> assumption)
