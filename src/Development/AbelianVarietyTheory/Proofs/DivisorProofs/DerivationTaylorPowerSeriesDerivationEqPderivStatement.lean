module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderiv
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

open IsLocalRing GlobalTheory.FormalOrigin

theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv (R := B) a (taylor ev (fun i => ⇑(ds i)) f) := by
  first | exact @GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | exact GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | (intros; apply GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv <;> assumption)
