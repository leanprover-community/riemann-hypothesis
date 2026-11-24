module

public import Formalism.MahlerMeasure.GoodCount
public import Formalism.MahlerMeasure.StatementD
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
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset

def GramWindow2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (n del h Y0 : ℕ) (k : ℤ) (La0 : ℝ) (t0 : ℕ)
    (Ψ : ℕ → MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p]) (e : Fin n → MvPolynomial σ ℚ_[p])
    (s : ℕ → ℚ_[p]) (c : Fin n → Fin n → ℕ → ℚ_[p]),
    LinearIndependent ℤ_[p] e →
    (∀ j (a : ℚ_[p]) u v, Ψ j (a • u) v = a * Ψ j u v) → (∀ j u u' v, Ψ j (u + u') v = Ψ j u v + Ψ j u' v) →
    (∀ j (a : ℚ_[p]) u v, Ψ j u (a • v) = a * Ψ j u v) → (∀ j u v v', Ψ j u (v + v') = Ψ j u v + Ψ j u v') →
    0 < Y0 → Y0 ≤ p ^ h → del + 1 ≤ p ^ h → 0 ≤ k → (∀ a b i, ‖c a b i‖ ≤ 1) →
    (Formalism.GM.binMatK ℚ_[p] del c).det ≠ 0 →
    -Real.logb p ‖(Formalism.GM.binMatK ℚ_[p] del c).det.leadingCoeff‖ +
        ((Formalism.GM.binMatK ℚ_[p] del c).det.natDegree : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La0 →
    (∀ j ∈ Finset.range Y0, s j ≠ 0 ∧ ‖s j‖ ≤ 1 ∧ ∀ a b,
      s j * Ψ j (e a) (e b) =
        ((Formalism.GM.binMatK ℚ_[p] del c).map (Polynomial.eval (((t0 + j : ℕ) : ℚ_[p])))) a b) →
    (∑ j ∈ Finset.range Y0, (Formalism.GM.M.bad p (Ψ j) (Submodule.span ℤ_[p] (Set.range e)) k : ℝ)) ≤
      (Y0 : ℝ) * ((n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / ((k : ℝ) + 1)))

end Formalism.MainNotions.G.GramWindowAlt

end
