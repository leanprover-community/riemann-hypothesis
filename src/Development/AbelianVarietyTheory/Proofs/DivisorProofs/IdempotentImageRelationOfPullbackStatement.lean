module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullback
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.idempotent_image_relation_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  first | (exact @GlobalTheory.UPel.HT.zRel_of_pullback) | (exact GlobalTheory.UPel.HT.zRel_of_pullback) | (intros; apply GlobalTheory.UPel.HT.zRel_of_pullback  <;> assumption)
