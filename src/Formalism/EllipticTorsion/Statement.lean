module

public import Formalism.FormalGroupLog.Statement
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.PowerSeries.Log
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

open Formalism.G

def legendre {K : Type u} [CommRing K] (l : K) : WeierstrassCurve K :=
  ⟨0, -(1 + l), 0, l, 0⟩

def deuring {K : Type u} [CommRing K] (a : K) : WeierstrassCurve K :=
  ⟨a, 0, 1, 0, 0⟩

def IntegralModel {K : Type u} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

def LegendreInv : Prop :=
  ∀ (K : Type u) [CommRing K] (l : K),
    (legendre l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 ∧ (legendre l).c₄ = 16 * (l ^ 2 - l + 1)

def DeuringInv : Prop :=
  ∀ (K : Type u) [CommRing K] (a : K),
    (deuring a).Δ = a ^ 3 - 27 ∧ (deuring a).c₄ = a * (a ^ 3 - 24)

def ModelLegendre : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K],
    ‖(2 : K)‖ = 1 → ∀ j : K, ‖j‖ ≤ 1 →
      ∃ l : K, ‖l‖ = 1 ∧ ‖l - 1‖ = 1 ∧
        (legendre l).c₄ ^ 3 = j * (legendre l).Δ ∧ ‖(legendre l).Δ‖ = 1

def ModelDeuring : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K],
    ‖(3 : K)‖ = 1 → ∀ j : K, ‖j‖ ≤ 1 →
      ∃ a : K, ‖a‖ ≤ 1 ∧
        (deuring a).c₄ ^ 3 = j * (deuring a).Δ ∧ ‖(deuring a).Δ‖ = 1

def ModelUnit : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (j : K), ‖j‖ ≤ 1 →
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j

def IntValuedZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [NormedAlgebra ℚ_[p] K]
    (P : Polynomial K), (∀ n : ℕ, ‖P.eval (n : K)‖ ≤ 1) →
      ∀ b : ℤ_[p], ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1

section Cong

variable {K : Type u} [NormedField K] [CharZero K] {σ : Type}

def logOnePlus (f : MvPowerSeries σ K) : MvPowerSeries σ K := (PowerSeries.log K).subst f

def InN (G : MvPowerSeries σ K) : Prop :=
  ∃ f : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 ∧ IntegralMv f ∧ G = logOnePlus f

def Cong (G H : MvPowerSeries σ K) : Prop := InN (G - H)

end Cong

def NAddSubgroup : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (σ : Type),
    InN (0 : MvPowerSeries σ K) ∧
    (∀ G H : MvPowerSeries σ K, InN G → InN H → InN (G + H)) ∧
    (∀ G : MvPowerSeries σ K, InN G → InN (-G))

def NZpSmul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CharZero K] [NormedAlgebra ℚ_[p] K] (σ : Type) (G : MvPowerSeries σ K), InN G →
      ∀ b : ℤ_[p], InN (algebraMap ℚ_[p] K (b : ℚ_[p]) • G)

def NPderiv : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (σ : Type)
    (G : MvPowerSeries σ K), InN G → ∀ i : σ, IntegralMv (MvPowerSeries.pderiv (R := K) i G)

end Formalism.ELL
