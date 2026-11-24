module

public import Formalism.PeriodIntegrals.AddIntG
public import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

def G (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  u ^ 3 + algebraMap ℂ_[p] R W.a₁ * u * v + algebraMap ℂ_[p] R W.a₂ * u ^ 2 * v +
    algebraMap ℂ_[p] R W.a₃ * v ^ 2 + algebraMap ℂ_[p] R W.a₄ * u * v ^ 2 +
    algebraMap ℂ_[p] R W.a₆ * v ^ 3 - v

def Gu (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  3 * u ^ 2 + algebraMap ℂ_[p] R W.a₁ * v + 2 * algebraMap ℂ_[p] R W.a₂ * u * v +
    algebraMap ℂ_[p] R W.a₄ * v ^ 2

def Gv (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  algebraMap ℂ_[p] R W.a₁ * u + algebraMap ℂ_[p] R W.a₂ * u ^ 2 + 2 * algebraMap ℂ_[p] R W.a₃ * v +
    2 * algebraMap ℂ_[p] R W.a₄ * u * v + 3 * algebraMap ℂ_[p] R W.a₆ * v ^ 2 - 1

def wser (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] := PowerSeries.X ^ 3 * wq

def wv (wq : PowerSeries ℂ_[p]) (i : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p] :=
  PowerSeries.subst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) (wser wq)

def lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  fun e => PowerSeries.coeff (e 0 + e 1 + 1) (wser wq)

def nu (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  wv wq 0 - lam wq * Xv 0

abbrev cc (a : ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] := algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) a

def Acf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  1 + cc W.a₂ * lam wq + cc W.a₄ * lam wq ^ 2 + cc W.a₆ * lam wq ^ 3

def Bcf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₁ * lam wq + cc W.a₂ * nu wq + cc W.a₃ * lam wq ^ 2 + 2 * cc W.a₄ * lam wq * nu wq +
    3 * cc W.a₆ * lam wq ^ 2 * nu wq

def Ccf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₁ * nu wq + 2 * cc W.a₃ * lam wq * nu wq + cc W.a₄ * nu wq ^ 2 +
    3 * cc W.a₆ * lam wq * nu wq ^ 2 - lam wq

def Dcf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₃ * nu wq ^ 2 + cc W.a₆ * nu wq ^ 3 - nu wq

def Z3 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  -Xv 0 - Xv 1 - Bcf W wq * (Acf W wq)⁻¹

def Fch (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then (0 : MvPowerSeries (Fin 2) ℂ_[p]) else Z3 W wq) (Z3 W wq)

end PI.AddIntG.Wk
