module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.ExpDeriv

open Filter Topology GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def expGL (X : Lie E a) (t : ℝ) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp (t • Matrix.of X)).unit

theorem expGL_val (X : Lie E a) (t : ℝ) :
    ((expGL X t : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = NormedSpace.exp (t • Matrix.of X) := rfl

theorem expGL_zero (X : Lie E a) : expGL X 0 = 1 :=
  Units.ext (by rw [expGL_val, zero_smul, NormedSpace.exp_zero]; rfl)

theorem expGL_add (X : Lie E a) (s t : ℝ) : expGL X (s + t) = expGL X s * expGL X t := by
  apply Units.ext
  rw [Units.val_mul, expGL_val, expGL_val, expGL_val, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)

theorem hasDerivAt_expGL (X : Lie E a) : HasDerivAt (fun t => toL (expGL X t).val) X 0 := by
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.of X) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_along (X : Lie E a) (ψ : Sm E a) (g : GA E a) (t : ℝ) :
    HasDerivAt (fun s => ψ.1 (g * infGL E a (expGL X s)))
      ((lie E a X ψ).1 (g * infGL E a (expGL X t))) t := by
  have h := hasDerivAt_curve ψ (g * infGL E a (expGL X t)) (expGL X) X (expGL_zero X) (hasDerivAt_expGL X)
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h)
  have e : (fun s => ψ.1 (g * infGL E a (expGL X s))) =
      fun x => ψ.1 (g * infGL E a (expGL X t) * infGL E a (expGL X (x - t))) := by
    funext s
    rw [mul_assoc, ← map_mul, ← expGL_add, add_sub_cancel]
  rw [e]
  exact h2

end GlobalTheory.ExpDeriv

namespace GlobalTheory.ExpDeriv

open Filter Topology GlobalTheory.CuspRep

end GlobalTheory.ExpDeriv

end
