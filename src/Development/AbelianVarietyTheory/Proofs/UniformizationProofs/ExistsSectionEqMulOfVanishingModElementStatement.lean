module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_eq_mul_of_vanishing_mod_element : ∀ (A A₀ A' : Type) [CommRing A] [CommRing A₀] [CommRing A'] (g₀ : A →+* A₀) (g' : A →+* A') (a : A), Function.Surjective g₀ → Function.Surjective g' → IsNilpotent (RingHom.ker g₀) → RingHom.ker g' = Ideal.span {a} → a ∈ RingHom.ker g₀ → (∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) → ∀ (X X₀ X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f' : X' ⟶ Spec (CommRingCat.of A')) (j₀ : X₀ ⟶ X) (β : X' ⟶ X), Flat f → IsPullback j₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → ∀ (N : LB X) (N₀ : LB X₀) (w₀ : LB.Iso N₀ (N.pull j₀)), N.IsLB → N₀.IsLB → w₀.IsGen → ∀ σ : LB.Sec N, (∀ k, (β.app (N.U k)).hom (σ.f k) = 0) → ∃ τ₀ : LB.Sec N₀, ∀ τ : LB.Sec N, (∀ z (k : (N).ι) (k' : (N₀).ι), (j₀) z ∈ (N).U k → z ∈ (N₀).U k' → gs (j₀) z _ ((τ).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ₀).f k')) → ∀ k, σ.f k = cst f (N.U k) a * τ.f k := by
  first | exact @GlobalTheory.SectionKernel.exists_sec_of_vanishing | exact GlobalTheory.SectionKernel.exists_sec_of_vanishing | (intros; apply GlobalTheory.SectionKernel.exists_sec_of_vanishing <;> assumption)
