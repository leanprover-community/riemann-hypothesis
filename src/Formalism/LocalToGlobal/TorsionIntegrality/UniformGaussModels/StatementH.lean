module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
public import Formalism.GaussJetBounds.StatementI
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
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
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

def IntOpTwoOrth : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → HasCMBy d L →
  ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W → ‖W.a₁‖ = 1 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → omegaK d * (ω₀ / 2) ∉ L.lattice → conj (omegaK d) * (ω₀ / 2) ∉ L.lattice →
  ∀ (n : Type) [Fintype n] (κ : Type) [Fintype κ] (r : κ → ℂ_[2]) (s : κ → n → ℂ) (N : ℕ),
    (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 2 ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (thetaZ 2 L ι ω₀ r s) ∧
    ∀ P : MvPolynomial n ℂ_[2], (∀ m, ‖AddMonoidAlgebra.coeff P m‖ ≤ 1) →
      ‖jetPair P (thetaZ 2 L ι ω₀ r s)‖ ≤ 1

def GoodModelTwo : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      Unif 2 (Formalism.L2.Th1.F.scalePair L c hc) ι W ∧ IntCurve W ∧ ‖W.a₁‖ = 1

end Formalism.L2.Th1.Top
