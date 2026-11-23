module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassTorsionConjTransport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.eisenstein_weierstrass_torsion_conj_transport : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ ω₀ ω₁ : ℂ, ω₀ = Ω₀ * c₀ / (2 * Real.pi * Complex.I) → ω₁ = Ω₁ * c₁ / (2 * Real.pi * Complex.I) → ω₀ ≠ 0 ∧ ω₁ ≠ 0 ∧ g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 ∧ g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 ∧ g (G2s τ₀ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₀ ^ 2) = G2s τ₁ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₁ ^ 2 ∧ ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), (∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') ∧ ∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3 := by
  first | exact @GlobalTheory.WpFam.Transp.main | exact GlobalTheory.WpFam.Transp.main | (intros; apply GlobalTheory.WpFam.Transp.main <;> assumption)
