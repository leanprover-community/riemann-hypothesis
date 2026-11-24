module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

def IntModel {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

def BridgeWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    Formalism.L2.Th1.B.IsWp (g₂ W) (g₃ W) (wpReg W)

def BridgeLaw : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.LawLog (fgl W) (logSer W) ∧ Formalism.L2.Th1.B.IsInv (logSer W) (iSer W) ∧
    (‖(2 : K)‖ = 1 → Formalism.L2.Th1.B.IsHalf (logSer W) (halfSer W))

def BridgeCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp (fgl W) (iSer W) (logSer W) (wpReg W) (xS W) (W.b₂ / 12)

end Formalism.L2.Th1.A
