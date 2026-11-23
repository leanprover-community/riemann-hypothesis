module

public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePower
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

theorem _root_.GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power : ∀ (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ) (w : WeightFamilies.Wt D j) (a b : ℕ), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | exact GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | (intros; apply GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow <;> assumption)
