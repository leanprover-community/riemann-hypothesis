module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
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

noncomputable section

namespace GlobalTheory.Honda

open PowerSeries

variable {K : Type} [NormedField K]

def Unr (K : Type) [NormedField K] (l : ℕ) (σ : K →+* K) : Prop :=
  l.Prime ∧ 2 < l ∧ ‖(l : K)‖ < 1 ∧ (∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : K)‖) ∧ (∀ x : K, ‖σ x‖ = ‖x‖) ∧
    ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ < 1

def ResAlg (K : Type) [NormedField K] : Prop :=
  ∀ f : Polynomial K, f.Monic → 0 < f.natDegree → (∀ n, ‖f.coeff n‖ ≤ 1) → ∃ x : K, ‖x‖ ≤ 1 ∧ ‖f.eval x‖ < 1

def CoefLe (r : ℝ) (f : K⟦X⟧) : Prop := ∀ n, ‖coeff n f‖ ≤ r

def frobOp (τ : K →+* K) (q i : ℕ) (f : K⟦X⟧) : K⟦X⟧ :=
  (PowerSeries.map (τ ^ i) f).subst ((X : K⟦X⟧) ^ (q ^ i))

def hondaSum (τ : K →+* K) (q : ℕ) (c : ℕ → K) (f : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range n, c j * coeff n (frobOp τ q (j + 1) f)

def IntLog [IsUltrametricDist K] (f e : K⟦X⟧) : Prop :=
  Formalism.L2.Th1.C.IsLogPair f e ∧ CoefLe 1 (derivative f) ∧ Formalism.L2.Th1.C.FGInt (Formalism.G.unitBall K) f e


open Formalism.L2.Th1.CM in
def EndOmega : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → (¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) →
    ∀ (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]), IsGoodModel l L ι g2 g3 →
      ∀ n : ℕ, ‖coeff n ((uSer g2 g3).subst
        (C (ι (omegaK d)) * Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)))‖ ≤ 1

end GlobalTheory.Honda
