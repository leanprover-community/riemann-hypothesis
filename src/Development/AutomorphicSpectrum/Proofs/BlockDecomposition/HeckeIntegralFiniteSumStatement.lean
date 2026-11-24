module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSum
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.hecke_integral_finite_sum : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → (∀ l ∈ L, ∀ x, u (x * l) = u x) → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ p : H ⧸ L, u p.out := by
  first | exact @GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall | exact GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall | (intros; apply GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall <;> assumption)
