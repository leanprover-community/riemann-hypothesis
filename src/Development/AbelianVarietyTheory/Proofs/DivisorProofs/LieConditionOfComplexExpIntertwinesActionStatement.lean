module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesAction
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lieCondition_of_complexExp_intertwines_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension D.g A.hom → IsExp (𝟙 (Sp ℂ)) e → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → b.IsType σ ρ → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ) (β : R →+* k), x ≫ spMap σ = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  first | exact @GlobalTheory.UPel.HT.lie_of_complexExp | exact GlobalTheory.UPel.HT.lie_of_complexExp | (intros; apply GlobalTheory.UPel.HT.lie_of_complexExp <;> assumption)
