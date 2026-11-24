module

public import Formalism.EllipticTorsion.WChordSeries
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

def wU {K : Type u} [Field K] (w : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => coeff (n + 3) w

def invSer {K : Type u} [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) : PowerSeries K :=
  X * (-1 + C W.a₁ * X + C W.a₃ * w)⁻¹

abbrev coeffRing {K : Type u} [Field K] (W : WeierstrassCurve K) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)

def CubeTwo : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    WFixed W w → MvPowerSeries.constantCoeff F = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F →
    let a : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
    let b : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
    ∃ c : MvPowerSeries (Fin 2) K, (∀ d, MvPowerSeries.coeff d c ∈ coeffRing W) ∧
      MvPowerSeries.constantCoeff c = -1 ∧
      b ^ 2 * ((wU w).subst a)⁻¹ - a ^ 2 * ((wU w).subst b)⁻¹
        = c * F * MvPowerSeries.subst ![a, (invSer W w).subst b] F

def CubeThree : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    WFixed W w → MvPowerSeries.constantCoeff F = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F →
    let t : Fin 3 → MvPowerSeries (Fin 3) K := fun i => MvPowerSeries.X i
    let row : Fin 3 → Fin 3 → MvPowerSeries (Fin 3) K := fun i =>
      ![t i ^ 3, t i * ((wU w).subst (t i))⁻¹, -((wU w).subst (t i))⁻¹]
    ∃ e : MvPowerSeries (Fin 3) K, (∀ d, MvPowerSeries.coeff d e ∈ coeffRing W) ∧
      MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of row).det
        = e * MvPowerSeries.subst ![MvPowerSeries.subst ![t 0, t 1] F, t 2] F
            * (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2)

end Formalism.ELL
