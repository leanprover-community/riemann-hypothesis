module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardPrimesOverEqFinrankOfTrivialFrobenius
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

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) → (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧ ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem | exact GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem | (intros; apply GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem <;> assumption)
