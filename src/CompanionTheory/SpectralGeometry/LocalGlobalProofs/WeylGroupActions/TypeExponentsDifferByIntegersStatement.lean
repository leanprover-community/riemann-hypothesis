module

public import Formalism.HermitianCurvature.StatementQ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsDifferByIntegers
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

theorem _root_.GlobalTheory.T.type_exponents_differ_by_integers : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, ∃ N : ℤ, u i - u j = (N : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.GapInt.type_param_diff_int | exact GlobalTheory.CompanionTheory.GapInt.type_param_diff_int | (intros; apply GlobalTheory.CompanionTheory.GapInt.type_param_diff_int <;> assumption)
