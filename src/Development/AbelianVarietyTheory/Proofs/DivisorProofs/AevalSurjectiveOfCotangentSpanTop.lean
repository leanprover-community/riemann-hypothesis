module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanSubMemSq
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

@[expose] public section

open GlobalTheory
open scoped Pointwise

namespace GlobalTheory.NakAug

theorem surj : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first
  | exact @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | (apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective ..)

end GlobalTheory.NakAug
