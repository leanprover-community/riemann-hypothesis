module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]

namespace BdRPlus

def thetaC : BdRPlus p O →+* C :=
  (IsUnitBall.awayEquiv O p).toRingEquiv.toRingHom.comp (theta p O)

variable {p O}

theorem thetaC_apply (x : BdRPlus p O) :
    thetaC p O x = IsUnitBall.awayEquiv O p (theta p O x) := rfl

@[simp] theorem thetaC_algebraMap (x : Ainf p O) :
    thetaC p O (algebraMap _ _ x) = (Ainf.theta p O x : C) := by
  rw [thetaC_apply, IsScalarTower.algebraMap_apply (Ainf p O) (AinfInv p O), theta_algebraMap,
    AinfInv.theta_algebraMap, IsUnitBall.awayEquiv_algebraMap]

theorem ker_thetaC : RingHom.ker (thetaC p O) = RingHom.ker (theta p O) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, thetaC_apply,
    map_eq_zero_iff _ (IsUnitBall.awayEquiv O p).injective]

variable [IsAlgClosed C]

section General

variable {F : Type v} {L : Type w} [Field F] [Field L] [Algebra F L] [CharZero F]
  [Algebra.IsAlgebraic F L]

end General

end BdRPlus

section Padic

variable [NormedAlgebra ℚ_[p] C]



variable [IsAlgClosed C] {L : Type w} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]

variable {p O}

end Padic

section Witt

variable [IsAlgClosed C] {k : Type v} [Field k] [CharP k p] [PerfectRing k p]
variable {L : Type w} [Field L] [Algebra (FractionRing (WittVector p k)) L]
  [Algebra.IsAlgebraic (FractionRing (WittVector p k)) L]

omit [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)] [IsUnitBall O] [IsAlgClosed C] in
theorem charZero_wittVector : CharZero (WittVector p k) := by
  refine ⟨fun m n h => ?_⟩
  have hinj : Function.Injective ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact Nat.cast_injective (R := ℤ_[p]) (hinj (by rw [map_natCast, map_natCast, h]))

instance : CharZero (FractionRing (WittVector p k)) :=
  haveI := charZero_wittVector p (k := k)
  inferInstance

variable {p O}

end Witt

end Reformulated.AutPerF
