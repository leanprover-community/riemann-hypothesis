module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
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

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

def HalfExists : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l : PowerSeries K), LawLog F l → ‖(2 : K)‖ = 1 → ∃ h, IsHalf l h

def SimeqInt : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (f g f' g' : MvPowerSeries ι K),
    Simeq f g → Simeq f' g' →
    Simeq (f - f') (g - g') ∧ Simeq (-f) (-g) ∧ ∀ n : ℤ, Simeq ((n : MvPowerSeries ι K) * f) (n * g)

def SimeqLog : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g : MvPowerSeries ι K),
    MvPowerSeries.constantCoeff g = 1 → Integral g → Simeq (fLog g) 0 ∧ Simeq (-fLog g) 0

def PhODef : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s2 : K) (P l : PowerSeries K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    PowerSeries.constantCoeff (phO s2 P l) = 0 ∧
      PowerSeries.subst l (sgStar s2 P) = PowerSeries.X * fExp (-phO s2 P l)

def PhEDef : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s2 e1 kap : K) (w l : PowerSeries K),
    PowerSeries.constantCoeff l = 0 →
    PowerSeries.constantCoeff (phE s2 e1 kap w l) = 0 ∧
      PowerSeries.subst l
          (sigma1 e1 kap w * fExp (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2))) =
        fExp (-phE s2 e1 kap w l)

def ParE : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A kap e1 s2 : K)
    (w l i : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsW A kap w → LawLog F l → IsInv l i → ‖kap‖ ≤ 1 →
    Integral (ι := Unit) (PowerSeries.subst l w) →
    Simeq (par F i (phE s2 e1 kap w l)) 0

def ParO : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 →
    Simeq (par F i (phO s2 P l)) 0

def WIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (c0 e1 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    LawLog F l → CurveHyp F i l P ep c0 → ‖c0 - e1‖ ≤ 1 →
    PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) =
        PowerSeries.X ^ 2 ∧
      Integral (ι := Unit) (PowerSeries.subst l (wOf e1 P))

def DiffPh : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 e1 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → 4 * e1 ^ 3 - g2 * e1 - g3 = 0 → LawLog F l → CurveHyp F i l P ep c0 →
    2 * (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l - phO s2 P l) =
        -fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) ∧
      (‖c0 - e1‖ ≤ 1 →
        Simeq (ι := Unit) (2 * phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l) (2 * phO s2 P l))

def CobRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → PowerSeries.constantCoeff f = 0 →
    DivAB (cob F f) ∧ swap2 (cob F f) = cob F f

def Cube : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l i f : PowerSeries K), LawLog F l → IsInv l i → ‖(2 : K)‖ = 1 →
    Simeq (par F i f) 0 → Simeq (d1 F (cob F f)) 0

def LogSigmaPullbackCocycle : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 : K)
    (P l i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → CurveHyp F i l P ep c0 → ‖(2 : K)‖ = 1 →
    DivAB (cob F (phO s2 P l)) ∧ swap2 (cob F (phO s2 P l)) = cob F (phO s2 P l) ∧
      Simeq (d1 F (cob F (phO s2 P l))) 0 ∧ Simeq (d1 F (swap2 (cob F (phO s2 P l)))) 0

def JetsThree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l f : PowerSeries K), LawLog F l → Simeq (d1 F (cob F f)) 0 →
    ∀ n : ℕ, 3 ≤ n → ‖PowerSeries.constantCoeff ((Dinv l)^[n] f)‖ ≤ 1

end Formalism.L2.Th1.B
