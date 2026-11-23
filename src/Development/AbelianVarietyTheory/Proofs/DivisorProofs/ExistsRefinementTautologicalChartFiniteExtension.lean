module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.taut_refine : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}, 1 ≤ n → ∀ C : Taut ζ g n φ, IsCN C.R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : C.R →+* R₁) (D : DegData R₁ (maximalIdeal R₁)) (e' : D.toPre.X ≃+ C.Q.X), IsCN R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ Refines C.Q ρ D.toPre e' := by
  intro o _ ζ g n φ hn C hCN
  obtain ⟨hmono, -, hcone, hdef, ht0⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ hn C
  have hsymm : ∀ i y z, ((n : ℤ) • C.δ i) y z = ((n : ℤ) • C.δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, mem_balForms_int.1 (hcone.mem i) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • C.δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hcone.nonneg i y)
  have hdef' : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • C.δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    refine ⟨i, ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hn) hi
  obtain ⟨R', _, _, _, ρ, -, D, e, hCN', hinj, hfin, hloc, -, href, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised C.R C.Q C.m C.t (fun i => (n : ℤ) • C.δ i) hCN hmono C.bd ht0 hsymm hnn hdef'
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, D, e, hCN', hinj, hfin, hloc, href⟩
