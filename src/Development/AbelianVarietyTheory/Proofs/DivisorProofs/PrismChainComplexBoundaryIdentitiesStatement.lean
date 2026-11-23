module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismChainComplexBoundaryIdentities
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.prism_chain_complex_boundary_identities : (∀ N (c : Pr N →₀ ℤ), Pr.d N (Pr.d N c) = 0) ∧ (∀ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) c, Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c)) ∧ (∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.Deg k (Pr.d N c)) ∧ (∀ N k (c : Pr N →₀ ℤ), Pr.Deg k c → Pr.Deg k (Pr.bd c)) ∧ (∀ N (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0) ∧ (∀ N (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)) ∧ ∀ N, Pr.Deg N (Pr.aw N) ∧ Pr.Deg N (Pr.wa N) := by
  first | (exact @GlobalTheory.EtC.PrCx.pr_complex) | (exact GlobalTheory.EtC.PrCx.pr_complex) | (intros; apply GlobalTheory.EtC.PrCx.pr_complex  <;> assumption)
