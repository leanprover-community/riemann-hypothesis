module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementG
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

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def WpCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (wpReg W) = 0 ∧ (∀ n : ℕ, Odd n → coeff n (wpReg W) = 0) ∧
    (-2 + X ^ 3 * derivative (wpReg W)) ^ 2 =
      4 * (1 + X ^ 2 * wpReg W) ^ 3 - C (g₂ W) * X ^ 4 * (1 + X ^ 2 * wpReg W) - C (g₃ W) * X ^ 6

def WpInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 2 * (1 + logSer W ^ 2 * (wpReg W).subst (logSer W)) =
      logSer W ^ 2 * (xS W + C (W.b₂ / 12) * X ^ 2)

def TInZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP : K),
    (tS W xP).subst (expSer W) * (1 + X ^ 2 * wpReg W - C (xP + W.b₂ / 12) * X ^ 2) = X ^ 2

def CubeTwoR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ c : MvPowerSeries (Fin 2) R, MvPowerSeries.constantCoeff c = -1 ∧
      U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) R)
        - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) R)
        = c * fgl W * MvPowerSeries.subst
            (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) R)] :
              Fin 2 → MvPowerSeries (Fin 2) R) (fgl W)

def CubeThreeR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    let t : Fin 3 → MvPowerSeries (Fin 3) R := fun i => MvPowerSeries.X i
    let row : Fin 3 → Fin 3 → MvPowerSeries (Fin 3) R := fun i =>
      ![t i ^ 3, t i * (xS W).subst (t i), (yS W).subst (t i)]
    ∃ e : MvPowerSeries (Fin 3) R, MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of row).det
        = e * MvPowerSeries.subst
              (![MvPowerSeries.subst (![t 0, t 1] : Fin 2 → MvPowerSeries (Fin 3) R) (fgl W), t 2] :
                Fin 2 → MvPowerSeries (Fin 3) R) (fgl W)
            * (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2)

def CoeffMem : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (S : Subring R),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ n, coeff n (wSer W) ∈ S) ∧ (∀ n, coeff n (xS W) ∈ S) ∧ (∀ n, coeff n (yS W) ∈ S) ∧
    (∀ n, coeff n (fw W) ∈ S) ∧ (∀ n, coeff n (om W) ∈ S) ∧ (∀ n, coeff n (iSer W) ∈ S) ∧
    (∀ d, MvPowerSeries.coeff d (fgl W) ∈ S) ∧ (∀ (k : ℤ) n, coeff n (zSer W k) ∈ S) ∧
    ((∃ h ∈ S, 2 * h = 1) → ∀ n, coeff n (halfSer W) ∈ S) ∧
    (∀ xP ∈ S, ∀ n, coeff n (tS W xP) ∈ S) ∧
    (∀ xP ∈ S, ∀ yP ∈ S, ∀ n, coeff n (xPlus W xP yP) ∈ S ∧ coeff n (yPlus W xP yP) ∈ S)

end Formalism.L2.Th1.A
