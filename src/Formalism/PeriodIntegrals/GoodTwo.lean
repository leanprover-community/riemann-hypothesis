module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
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
open scoped ComplexConjugate

namespace PI.GoodTwo

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

def IntCurve {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1 ∧ ‖W.Δ‖ = 1

def Half : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      (W.c₄ / 12 = ι (scalePair L c hc).g₂ ∧ W.c₆ / 216 = ι (scalePair L c hc).g₃) ∧ IntCurve W

def Full : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      (W.c₄ / 12 = ι (scalePair L c hc).g₂ ∧ W.c₆ / 216 = ι (scalePair L c hc).g₃) ∧ IntCurve W ∧ ‖W.a₁‖ = 1

def Twist : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K) (g2 g3 : K),
    W.Δ ≠ 0 → g2 ^ 3 - 27 * g3 ^ 2 ≠ 0 → W.c₄ ^ 3 * (g2 ^ 3 - 27 * g3 ^ 2) = 1728 * g2 ^ 3 * W.Δ →
    ∃ u : K, u ≠ 0 ∧ W.c₄ / 12 = u ^ 4 * g2 ∧ W.c₆ / 216 = u ^ 6 * g3

def JUnit : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2], ‖ι (jInv L)‖ = 1

def disc (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

def IsIdxTwo (L L' : PeriodPair) : Prop :=
  ∃ t : ℂ, t ∉ L.lattice ∧ 2 * t ∈ L.lattice ∧ ∀ z, z ∈ L'.lattice ↔ (z ∈ L.lattice ∨ z - t ∈ L.lattice)

def TwoIsog : Prop :=
  ∀ L L' : PeriodPair, IsIdxTwo L L' → (disc L' + 16 * disc L) ^ 3 = jInv L * disc L' * disc L ^ 2

def NormPow : Prop :=
  ∀ d : ℕ, Squarefree d → d % 8 = 7 →
    ∃ (h : ℕ) (x y : ℤ), 0 < h ∧ Odd y ∧ x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h

def Chain : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → HasCMBy d L → ∀ (h : ℕ) (x y : ℤ), Odd y →
    x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h → ∀ π : ℂ, (π = x + y * omegaK d ∨ π = x + y * conj (omegaK d)) →
    ∃ M : ℕ → PeriodPair, M 0 = L ∧ (∀ i, HasCMBy d (M i)) ∧ (∀ i, i < h → IsIdxTwo (M i) (M (i + 1))) ∧
      ∀ z, z ∈ (M h).lattice ↔ π * z ∈ L.lattice

end PI.GoodTwo
