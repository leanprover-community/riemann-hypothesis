module

public import Formalism.MahlerMeasure.IsFrozenInv
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

namespace Formalism.GM.M

open MvPolynomial Finset

def HasOrder {σ : Type} {p : ℕ} [Fact p.Prime] (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) : Prop :=
  (∀ m ∈ f.support, e ≤ m v) ∧ ∃ m ∈ f.support, m v = e

noncomputable def initPart {σ : Type} {p : ℕ} [Fact p.Prime] (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) :
    MvPolynomial σ ℚ_[p] :=
  ∑ m ∈ f.support, if m v = e then monomial m (f.coeff m) else 0

noncomputable def tieGam (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) : ℚ_[p] :=
  (((LL.deg (Fin.last N) + n + r + z - 1).choose (LL.deg (Fin.last N)) : ℕ) : ℚ_[p]) *
    fock p (tiePhiAt p (LL.snoc n) (Fin.castSucc (Fin.last N)) (Fin.last (N + 1)) z (freeze p LL ρ n f))
      (freeze p LL ρ n f') /
    ((((n - LL.total).factorial * LL.total.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p]))

def GamDeg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z e e' : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ Pol p r LL → f' ∈ Pol p r LL →
    HasOrder (Fin.last N, ρ) e f → HasOrder (Fin.last N, ρ) e' f' →
    ∃ P : Polynomial ℚ_[p], P.natDegree ≤ LL.total + LL.deg (Fin.last N) - max e e' ∧
      ∀ n, LL.total ≤ n → tieGam p LL ρ z n f f' = P.eval (n : ℚ_[p])

def GamLead : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (P : Polynomial ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ Pol p r LL → f' ∈ Pol p r LL →
    HasOrder (Fin.last N, ρ) e f → HasOrder (Fin.last N, ρ) e f' →
    (∀ n, LL.total ≤ n → tieGam p LL ρ z n f f' = P.eval (n : ℚ_[p])) →
    P.coeff (LL.total + LL.deg (Fin.last N) - e) =
      ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) *
        fock p (initPart (Fin.last N, ρ) e f) (initPart (Fin.last N, ρ) e f') /
        ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℚ_[p]) *
          ∏ i, ((LL.deg i).factorial : ℚ_[p]))

end Formalism.GM.M
