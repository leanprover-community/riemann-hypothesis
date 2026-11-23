module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightPreservingPartNonLoweringUnit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

theorem _root_.GlobalTheory.T.exists_weightPreservingPart_nonLowering_unit : ∀ {S ι : Type} [Ring S] [Fintype ι] (st : S →+ S) (ε : ι → S) (w : ι → ℤ) (τ : ι → ι), (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → CompleteOrthogonalIdempotents ε → (∀ a, st (ε a) = ε (τ a)) → (∀ a, w (τ a) = -w a) → (∀ a, τ (τ a) = a) → ∀ x y : S, x * y = 1 → y * x = 1 → st x = y → (∀ a b, w a < w b → ε a * x * ε b = 0) → (∀ a b, w a < w b → ε a * y * ε b = 0) → ∃ m m' : S, m * m' = 1 ∧ m' * m = 1 ∧ st m = m' ∧ (∀ a b, w a ≠ w b → ε a * m * ε b = 0) ∧ (∀ a b, w a ≠ w b → ε a * m' * ε b = 0) ∧ x * m' - 1 ∈ raise ε w 0 ∧ ∀ S₀ : Subring S, (∀ a, ε a ∈ S₀) → x ∈ S₀ → y ∈ S₀ → m ∈ S₀ ∧ m' ∈ S₀ := by
  first | exact @GlobalTheory.WeightPart.exists_weightPart | exact GlobalTheory.WeightPart.exists_weightPart | (intros; apply GlobalTheory.WeightPart.exists_weightPart <;> assumption)
