module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHom
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_dividedPowerEval_twoVars_ringHom : ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  first | exact @GlobalTheory.dpEval_two | exact GlobalTheory.dpEval_two | (intros; apply GlobalTheory.dpEval_two <;> assumption)
