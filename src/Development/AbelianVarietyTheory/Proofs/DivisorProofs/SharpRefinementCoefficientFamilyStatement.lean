module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementCoefficientFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sharp_refinement_coefficient_family : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (J : Type) (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∀ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
    ∃ v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀, t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) := by
  first | exact @GlobalTheory.Poinc.Sep.fibre_theta_consts_in_subfield | exact GlobalTheory.Poinc.Sep.fibre_theta_consts_in_subfield | (intros; apply GlobalTheory.Poinc.Sep.fibre_theta_consts_in_subfield <;> assumption)
