module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLiftBaseChangeH1VanishingTestRing
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

theorem _root_.GlobalTheory.T.exists_section_lift_baseChange_h1Vanishing_testRing : ∀ (A A' S : Type) [CommRing A] [CommRing A'] [CommRing S] (g' : A →+* A') (g : A →+* S), (∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) A) (D₁ : Matrix (Fin c) (Fin b) A), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) → ∀ v' : Fin a → A', (D₀.map g').mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, g' (v k) = v' k) → ∀ (X X' XS : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (fS : XS ⟶ Spec (CommRingCat.of S)) (β : X' ⟶ X) (σ : XS ⟶ X), Smooth f → IsProjBy f → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → IsPullback σ fS f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (X ⟶ W)) (φ' : K → (X' ⟶ W)) (ε : K → ℤ), L.IsLB → (∀ k, β ≫ φ k = φ' k) → FirstCohomologyVanishes ((LB.LinComb L φ ε).pull σ) → ∀ s' : LB.Sec (LB.LinComb L φ' ε), ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ z J, Good L z J → sval s β z J = sval s' (𝟙 _) z J := by
  first | exact @GlobalTheory.SecLift.exists_lift | exact GlobalTheory.SecLift.exists_lift | (intros; apply GlobalTheory.SecLift.exists_lift <;> assumption)
