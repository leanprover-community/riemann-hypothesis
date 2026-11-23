module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliLevelQuotientByFiniteGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.moduli_level_quotient_by_finite_group : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (k : KA l₀ →+* KA l₁), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k → r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k → LevComp (Xo l₁).univ (Xo l₀).univ r ν → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ →* Aut (Xo l₁).X) (τ : Γ →* Aut (Xo l₁).univ.t.G.left) (mu : ∀ g, SABMap (Xo l₁).univ.t (Xo l₁).univ.t (ρ g).asIso.hom), Function.Injective ρ ∧ (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : (Xo l₀).X.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ((Xo l₁).X, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) ∧ ∀ ω, (mu ω).φ = (τ ω).asIso.hom ∧ (τ ω).asIso.hom ≫ ν.φ = ν.φ ∧ (∀ x, ((Xo l₁).univ.eta x).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.eta x).left) ∧ ∃ (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l₁ ≃+* KA l₁), σ (baseKA l₁).ρ = (baseKA l₁).ρ ∧ (ρ ω).asIso.hom ≫ (Xo l₁).s = (Xo l₁).s ≫ spMap σ.toRingHom ∧ ∀ x, ((Xo l₁).univ.etaA (g x)).left ≫ (τ ω).asIso.hom = (ρ ω).asIso.hom ≫ ((Xo l₁).univ.etaA x).left :=
  GlobalTheory.LevQuot.exists_level_quotient
