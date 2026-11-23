module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatWeightDecreases
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

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

theorem _root_.GlobalTheory.T.bruhat_weight_decreases : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (t w w' b r i : GU σ n) (π π' : Equiv.Perm (Fin n)), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → IsPermW w π → IsPermW w' π' → IsBorelU b → r ∈ IwU σ n → i ∈ IwU σ n → w * r * t = b * w' * i → permWt t π' < permWt t π ∨ (π' = π ∧ ∀ a : Fin n, ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) = ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a))) := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.cell_triang | exact GlobalTheory.CompanionTheory.SatPow.cell_triang | (intros; apply GlobalTheory.CompanionTheory.SatPow.cell_triang <;> assumption)
