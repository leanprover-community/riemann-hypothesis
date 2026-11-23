module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementH
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.G (unitBall)

def ShapeAt {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K)
    (d : ℕ) : Prop :=
  ‖jet l ph 2‖ ≤ ‖(d : K)‖ ^ (-(1 / 2 : ℝ)) ∧ (∀ i : ℕ, 1 ≤ i → i ≠ 2 → ‖jet l ph i‖ ≤ 1) ∧
  ∃ J : PowerSeries K, JetsIn1 (unitBall K) J ∧ PowerSeries.constantCoeff J = 1 ∧
    PowerSeries.subst linv (mvExp (-ph) : PowerSeries K) =
      (mvExp (-(PowerSeries.C (jet l ph 2 / 2) * PowerSeries.X ^ 2)) : PowerSeries K) * J

def InvEndInt : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (l linv : PowerSeries K) (a : K),
    IsLogPair l linv → a ≠ 0 → a⁻¹ ∈ R → EndInt R l linv a → EndInt R l linv a⁻¹

def AdjUnitNorm : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K) (N : ℤ),
    Frame R l linv ph → F1 R l linv ph → a ≠ 0 → a⁻¹ ∈ R → EndInt R l linv a → EndInt R l linv b →
    a * b = (N : K) → PhNormAt R l linv ph a b → AdjAt R l linv ph a b

def HalfValuation : Prop :=
  ∀ (K : Type) [NormedField K] (S c : K) (d : ℕ), c ^ 2 = -(d : K) → (d : K) ≠ 0 → ‖c * S‖ ≤ 1 →
    ‖S‖ ≤ ‖(d : K)‖ ^ (-(1 / 2 : ℝ))

def RamifiedShape : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K)
    (a b : K) (d : ℕ),
    Frame (unitBall K) l linv ph → F1 (unitBall K) l linv ph →
    PhNormAt (unitBall K) l linv ph (-1) (-1) → ‖(2 : K)‖ = 1 →
    AdjAt (unitBall K) l linv ph a b → (a - b) ^ 2 = -(d : K) → d ≠ 0 →
    ShapeAt l linv ph d

def CurveNegNorm : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    (2 : K)⁻¹ ∈ R → ∀ s2 : K,
    PhNormAt R (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) (-1) (-1)

def WeierstrassBiadditiveModEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 → ∀ s2 : K,
    F1 (unitBall K) (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W))

def CurveRamified : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 →
    ∀ (s2 al albar : K) (d : ℕ) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al‖ = 1 → al + albar = (t : K) →
    (al - albar) ^ 2 = -(d : K) → d ≠ 0 → ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 →
    al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ShapeAt (logSer W) (expSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) d

end Formalism.L2.Th1.G
