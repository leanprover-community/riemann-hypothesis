module

public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.binaryHermitianForm_represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n → (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) → ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  first | exact @GlobalTheory.BinaryRep.represents_totallyPositive | exact GlobalTheory.BinaryRep.represents_totallyPositive | (intros; apply GlobalTheory.BinaryRep.represents_totallyPositive <;> assumption)
