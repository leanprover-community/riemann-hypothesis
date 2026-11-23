module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMinorsIffBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.integral_minors_iff_basis_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  first | exact @GlobalTheory.WeylLatDualProof.integral_minors_iff_basis | exact GlobalTheory.WeylLatDualProof.integral_minors_iff_basis | (intros; apply GlobalTheory.WeylLatDualProof.integral_minors_iff_basis <;> assumption)
