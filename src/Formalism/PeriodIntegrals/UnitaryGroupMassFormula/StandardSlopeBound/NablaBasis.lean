module

public import Formalism.GradedWeylDivisibility.StatementB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord

@[expose] public section

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

def gramOf {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Fin r → MvPolynomial (Fin N × Fin N) ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    fockQ (map (Int.castRingHom ℚ) (e i)) (map (Int.castRingHom ℚ) (e j)) / fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)

def MonoFactLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ), (∀ s, ∑ a, m (a, s) = ν s) →
    ∏ s, (ν s).factorial ≤ N ^ (∑ s, ν s) * ∏ k ∈ m.support, (m k).factorial

def NablaGramLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (r : ℕ) (e : Module.Basis (Fin r) ℤ (dualWeyl ℤ N N ν)), Antitone ν →
    (((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν))) ^ r ≤
      (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det

def GramDual : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (r r' : ℕ) (e : Module.Basis (Fin r) ℤ (weyl ℤ N N le_rfl ν))
    (e' : Module.Basis (Fin r') ℤ (dualWeyl ℤ N N ν)), Antitone ν →
    r = r' ∧ (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det *
      (gramOf ν fun i => (e' i : MvPolynomial (Fin N × Fin N) ℤ)).det = 1

def NablaBasis : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), ∃ (r : ℕ), Nonempty (Module.Basis (Fin r) ℤ (dualWeyl ℤ N N ν))

end PI.SlopeSteps
