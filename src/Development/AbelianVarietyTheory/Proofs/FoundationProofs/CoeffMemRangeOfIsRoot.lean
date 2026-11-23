module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbitStatement
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.PsRoot

theorem mem_of_isAlgebraic_of_isAlgClosed (E : Subfield ℂ) [IsAlgClosed E] {x : ℂ}
    (hx : IsAlgebraic E x) : x ∈ E := by
  have hi : IsIntegral E x := hx.isIntegral
  have h1 : (minpoly E x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

theorem coeff_mem_range_of_isRoot : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 →
    (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 →
    ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  intro Ω _ _ ε b Q hQ hcoef hb k
  let E : Subfield ℂ := ε.fieldRange
  haveI : IsAlgClosed E := IsAlgClosed.of_ringEquiv Ω E ε.rangeRestrictFieldEquiv
  have hE : ∀ z : ℂ, z ∈ ε.range → z ∈ E := fun z hz => by
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, rfl⟩

  have hroot : ∀ g : ℂ ≃ₐ[E] ℂ, Q.IsRoot (PowerSeries.map (g : ℂ →+* ℂ) b) := by
    intro g
    have hfix : Q.map (PowerSeries.map (g : ℂ →+* ℂ)) = Q := by
      ext i j
      rw [Polynomial.coeff_map, PowerSeries.coeff_map]
      obtain ⟨y, hy⟩ := hE _ (hcoef i j)
      rw [← hy]
      exact g.commutes ⟨_, ⟨y, rfl⟩⟩
    have h2 := Polynomial.eval_map_apply (PowerSeries.map (g : ℂ →+* ℂ)) (p := Q) b
    show Q.eval _ = 0
    rw [hfix, hb, map_zero] at h2
    exact h2
  have hfin : (Set.range fun g : ℂ ≃ₐ[E] ℂ => g (PowerSeries.coeff k b)).Finite := by
    refine ((Polynomial.finite_setOf_isRoot hQ).image (PowerSeries.coeff k)).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨PowerSeries.map (g : ℂ →+* ℂ) b, hroot g, ?_⟩
    simp [PowerSeries.coeff_map]
  obtain ⟨y, hy⟩ := mem_of_isAlgebraic_of_isAlgClosed E (GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit E _ hfin)
  exact ⟨y, hy⟩

end GlobalTheory.PsRoot
