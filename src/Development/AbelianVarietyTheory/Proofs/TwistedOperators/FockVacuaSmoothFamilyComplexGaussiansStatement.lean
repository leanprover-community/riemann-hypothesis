module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussians
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

open MeasureTheory

theorem _root_.GlobalTheory.T.fockVacua_smooth_family_complexGaussians : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.FockFamily.fock_vacua_family | exact GlobalTheory.FockFamily.fock_vacua_family | (intros; apply GlobalTheory.FockFamily.fock_vacua_family <;> assumption)
