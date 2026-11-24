module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.CuspidalSupport₂

variable {k : Type} [Field k]

theorem twist_detRep_one (χ η : kˣ →* ℂˣ) :
    twist (detRep (Fin 1) χ) (detChar (Fin 1) η) = detRep (Fin 1) (η * χ) := by
  have h : GlobalTheory.SmGL.detChar (Fin 1) η * GlobalTheory.SmGL.detChar (Fin 1) χ =
      GlobalTheory.SmGL.detChar (R := k) (Fin 1) (η * χ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply]
  unfold GlobalTheory.SmGL.detRep GlobalTheory.SmGL.ofChar
  rw [GlobalTheory.SmGL.twist_twist, h]

theorem twist_twist_inv {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (GL (Fin d) k) X) (η : kˣ →* ℂˣ) :
    twist (twist σ (detChar (Fin d) η⁻¹)) (detChar (Fin d) η) = σ := by
  have h : GlobalTheory.SmGL.detChar (Fin d) η * GlobalTheory.SmGL.detChar (Fin d) η⁻¹ =
      (1 : GL (Fin d) k →* ℂˣ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply, MonoidHom.inv_apply,
      mul_inv_cancel, MonoidHom.one_apply]
  rw [GlobalTheory.SmGL.twist_twist, h, GlobalTheory.SmGL.twist_one]

end UpperTheory.TNZ.CuspidalSupport₂

namespace UpperTheory.TNZ

end UpperTheory.TNZ
