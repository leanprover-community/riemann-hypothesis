module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDerivationsEqZeroKillingBothFactors
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pointDerivations_eq_zero_killing_both_factors : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (W₀ : Z.Opens), W₀ ≤ p ⁻¹ᵁ U.1 → ∀ (O : Z'.Opens), O ≤ φ ⁻¹ᵁ W₀ ⊓ p' ⁻¹ᵁ U'.1 → ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₀ : Sp S ⟶ Z'), ⊤ ≤ g₀ ⁻¹ᵁ O → ∀ (Δ : ∀ O' : Z'.Opens, Γ(Z', O') → S), (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f + f') = Δ O' f + Δ O' f') → (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f * f') = valR g₀ O' f * Δ O' f' + valR g₀ O' f' * Δ O' f) → (∀ (O₁ O₂ : Z'.Opens) (h : O₂ ≤ O₁), O₁ ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O₂ → ∀ f, Δ O₂ (resG Z' h f) = Δ O₁ f) → (∀ (O₀ : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O₀), O₀ ≤ W₀ → O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f₀, Δ O' ((φ.appLE O₀ O' h).hom f₀) = 0) → (∀ (O' : Z'.Opens) (h : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ r, Δ O' ((p'.appLE U'.1 O' h).hom r) = 0) → ∀ f, Δ O f = 0 := by
  first | exact @GlobalTheory.KSBaseChangeLocal.eq_zero_of_kills_both | exact GlobalTheory.KSBaseChangeLocal.eq_zero_of_kills_both | (intros; apply GlobalTheory.KSBaseChangeLocal.eq_zero_of_kills_both <;> assumption)
