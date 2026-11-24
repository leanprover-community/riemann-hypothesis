module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_invariance | exact GlobalTheory.Hk3.HoweDuality.latIdx_invariance | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_invariance <;> assumption)
