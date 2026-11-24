module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixExistsPrimePowClearsDenominatorsOver
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((((p ^ d : ℕ) : FiniteAdeleRing (𝓞 E) E) * A i j) Q) ≤ 1 := by
  first | exact @GlobalTheory.StdAtPrime.exists_pow_clears_denom_over | exact GlobalTheory.StdAtPrime.exists_pow_clears_denom_over | (intros; apply GlobalTheory.StdAtPrime.exists_pow_clears_denom_over <;> assumption)
