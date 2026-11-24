module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
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

noncomputable section

namespace Formalism.L2.Th1.E

section An

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

def curveL : WeierstrassCurve ℂ_[l] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃)


open Classical in
def ptOf (t : ℂ) : (curveL l L ι).toAffine.Point :=
  if h : t ∉ L.lattice ∧
      (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2)
  then .some _ _ h.2 else 0

def phL : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L))
    (Formalism.L2.Th1.A.logSer (curveL l L ι))

def inU (f : ℂ → ℂ) : PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 f)).subst (Formalism.L2.Th1.A.logSer (curveL l L ι))

def gT (t : ℂ) : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.fExp (phL l L ι) * inU l L ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L))

def phPrime (t₀ : ℂ) : PowerSeries ℂ_[l] :=
  -Formalism.L2.Th1.B.fLog (inU l L ι (Formalism.L2.Th1.F.th0 L t₀))

end An


def PtOfAdd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (s t : ℂ),
    ptOf l L ι (s + t) = ptOf l L ι s + ptOf l L ι t

def PtOfZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ), ptOf l L ι t = 0 ↔ t ∈ L.lattice

def TorsionIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K), IntCurve W →
    ∀ (P : W.toAffine.Point) (N : ℕ), ‖(N : K)‖ = 1 → N • P = 0 → P ≠ 0 → ‖px W P‖ ≤ 1 ∧ ‖py W P‖ ≤ 1

def WpBridge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]),
    Formalism.L2.Th1.A.wpReg (curveL l L ι) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L)

def TransWpBridge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ), t ∉ L.lattice →
    inU l L ι (fun z => L.weierstrassP (z + t)) = xT (curveL l L ι) (ptOf l L ι t)


def AnalyticSys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (π : ℂ →+ (curveL l L ι).toAffine.Point), (∀ t, π t = ptOf l L ι t) →
    IsTransSys (curveL l L ι) π (gT l L ι)

def AnalyticTrans : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
      OneUnit (C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0))⁻¹ * gT l L ι t)

def OpUTh0Root : Prop :=
  ∀ (L : PeriodPair) (t t₀ : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ L.lattice → (N : ℂ) * t₀ ∈ L.lattice →
    t₀ ∉ L.lattice → ∃ (ζ : ℂ) (m : ℕ), 0 < m ∧ ζ ^ m = 1 ∧
      Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.th0 L t₀) =
        fun z => ζ * (Formalism.L2.Th1.F.opU L t₀ (Formalism.L2.Th1.F.sgStar L) 0)⁻¹ *
          Formalism.L2.Th1.F.opU L (t + t₀) (Formalism.L2.Th1.F.sgStar L) z

def ThetaZeroAnalytic : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
      Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit) (phL l L ι) (phPrime l L ι (ω₀ / 2)) ∧
      ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice →
        GaussOne (Formalism.L2.Th1.B.fExp (phL l L ι) *
          inU l L ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

def PtOfInt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖px (curveL l L ι) (ptOf l L ι t)‖ ≤ 1 ∧ ‖py (curveL l L ι) (ptOf l L ι t)‖ ≤ 1

def KernelPtInt : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (a b : ℤ) (t : ℂ), ((a : ℂ) + (b : ℂ) * Formalism.L2.Th1.CM.omegaK d) * t ∈ L.lattice →
      ¬ (l : ℤ) ∣ a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) → t ∉ L.lattice →
      ‖px (curveL l L ι) (ptOf l L ι t)‖ ≤ 1 ∧ ‖py (curveL l L ι) (ptOf l L ι t)‖ ≤ 1

end Formalism.L2.Th1.E
