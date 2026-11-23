module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDeXExpand
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

theorem _root_.GlobalTheory.T.phi_DeX_expand_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  first | exact @GlobalTheory.WeylLatDualProof.phi_DeX_expand | exact GlobalTheory.WeylLatDualProof.phi_DeX_expand | (intros; apply GlobalTheory.WeylLatDualProof.phi_DeX_expand <;> assumption)
