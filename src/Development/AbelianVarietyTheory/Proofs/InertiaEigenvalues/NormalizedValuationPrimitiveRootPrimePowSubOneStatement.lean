module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
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


theorem _root_.GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l k : ℕ), l.Prime → 1 ≤ k → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ ζ : O, IsPrimitiveRoot ζ (l ^ k) → ζ - 1 ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (ζ - 1) = 1 / (Nat.totient (l ^ k) : ℝ) := by
  first | exact @GlobalTheory.nval_primitiveRoot_prime_pow_sub_one | exact GlobalTheory.nval_primitiveRoot_prime_pow_sub_one | (intros; apply GlobalTheory.nval_primitiveRoot_prime_pow_sub_one <;> assumption)
