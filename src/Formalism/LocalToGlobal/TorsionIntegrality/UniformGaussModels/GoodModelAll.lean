module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementR
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementP
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

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)

def thetaZ (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) (ω₀ : ℂ)
    {κ n : Type} [Fintype κ] [Fintype n] (r : κ → ℂ_[p]) (s : κ → n → ℂ) : MvPowerSeries n ℂ_[p] :=
  Formalism.L2.Th1.E.thetaProd r (fun k i => PowerSeries.map (ι : ℂ →+* ℂ_[p])
    (Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.opU L (s k i) (Formalism.L2.Th1.F.th0 L (ω₀ / 2)))))

def phC (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) : PowerSeries ℂ_[p] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (wpReg (curveL p L ι)) (logSer (curveL p L ι))

def GoodModelAll : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (c : ℂ) (hc : c ≠ 0), IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)

def CMDatum : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), IntCurve (curveL p L ι) →
  ∀ m n : ℤ, ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m n →
  ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
    Formalism.L2.Th1.C.IsEndoCurve (curveL p L ι) neg xP yP (ι ((m : ℂ) + (n : ℂ) * omegaK dK)) ∧
    (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
    ι ((m : ℂ) + (n : ℂ) * omegaK dK) * ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      (Fintype.card S : ℂ_[p]) + 1 ∧
    ι ((m : ℂ) + (n : ℂ) * omegaK dK) *
        (ι ((m : ℂ) + (n : ℂ) * omegaK dK) - ι ((m : ℂ) + (n : ℂ) * (1 - omegaK dK))) *
        ι (Formalism.L2.Th1.F.s2 L) = ∑ P, (xP P + (curveL p L ι).b₂ / 12)

def ShapeCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    Formalism.L2.Th1.G.ShapeAt (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) dK

def JetsCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    ∀ i : ℕ, 1 ≤ i → ‖Formalism.L2.Th1.C.jet (logSer (curveL p L ι)) (phC p L ι) i‖ ≤ 1

end Formalism.L2.Th1.Top
