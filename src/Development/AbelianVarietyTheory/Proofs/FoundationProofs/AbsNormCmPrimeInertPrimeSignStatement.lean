module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSign
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.absNorm_cmPrime_inertPrime_sign : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → Ev D (Ideal.absNorm P) ∧ (D.host.conj • P = P → sgn D (Ideal.absNorm P) = -1 ∧ ∃ q f : ℕ, q.Prime ∧ InertQ D q ∧ q ≠ 2 ∧ (q : 𝓞 D.host.E) ∈ P ∧ Odd f ∧ Ideal.absNorm P = q ^ (2 * f) ∧ (q ≠ D.host.d → ¬ IsSquare (-(D.host.d : ZMod q)))) ∧ (D.host.conj • P ≠ P → sgn D (Ideal.absNorm P) = 1 ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P → ¬ InertQ D q) := by
  first | exact @GlobalTheory.InertResidue.norm_prime | exact GlobalTheory.InertResidue.norm_prime | (intros; apply GlobalTheory.InertResidue.norm_prime <;> assumption)
