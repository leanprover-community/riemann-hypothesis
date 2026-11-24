module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
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

namespace UpperTheory.Ring.Comp

open Reformulated.AutPerF

abbrev Fl (l : ℕ) [Fact (Nat.Prime l)] : Type := Tilt l (PadicComplexInt l)

abbrev Ainf (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Ainf l (PadicComplexInt l)

abbrev AinfP (l : ℕ) [Fact (Nat.Prime l)] : Type := AinfInv l (PadicComplexInt l)

abbrev BdRp (l : ℕ) [Fact (Nat.Prime l)] : Type := BdRPlus l (PadicComplexInt l)

abbrev BdR (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.BdR l (PadicComplexInt l)

abbrev Acris0 (l : ℕ) [Fact (Nat.Prime l)] : Subalgebra (Ainf l) (AinfP l) := acrisZero l (PadicComplexInt l)

abbrev Acris (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Acris l (PadicComplexInt l)

abbrev Bcris (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Bcris l (PadicComplexInt l)

abbrev Gq (l : ℕ) [Fact (Nat.Prime l)] : Type := PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l

def zP (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* AinfP l := algebraMap ℤ_[l] (AinfP l)

def θP (l : ℕ) [Fact (Nat.Prime l)] : AinfP l →+* ℂ_[l] :=
  (IsUnitBall.awayEquiv (PadicComplexInt l) l).toRingEquiv.toRingHom.comp (AinfInv.theta l (PadicComplexInt l))

def pD (l : ℕ) [Fact (Nat.Prime l)] : AinfP l →+* BdR l :=
  (algebraMap (BdRp l) (BdR l)).comp (algebraMap (AinfP l) (BdRp l))

def zD (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* BdR l := (pD l).comp (zP l)

def aB (l : ℕ) [Fact (Nat.Prime l)] : Ainf l →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap (Ainf l) (Acris l))

def a0B (l : ℕ) [Fact (Nat.Prime l)] : Acris0 l →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap (AcrisZero l (PadicComplexInt l)) (Acris l))

def zB (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap ℤ_[l] (Acris l))

def σD {l : ℕ} [Fact (Nat.Prime l)] (g : Gq l) : BdR l →+* BdR l :=
  MulSemiringAction.toRingHom (Gq l) (BdR l) g

end UpperTheory.Ring.Comp
