module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationProd
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT


theorem _root_.GlobalTheory.T.exists_linearization_prod : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ga Gb : Type) [Group Ga] [Group Gb] (ρ₁ : Ga → (X ⟶ X)) (ρ₂ : Gb → (X ⟶ X)) (ρ : Ga × Gb → (X ⟶ X)), (∀ p, ρ p = ρ₁ p.1 ≫ ρ₂ p.2) → (∀ a b, ρ₁ a ≫ ρ₂ b = ρ₂ b ≫ ρ₁ a) → (∀ a c, ρ₁ (a * c) = ρ₁ a ≫ ρ₁ c) → (∀ b d, ρ₂ (b * d) = ρ₂ b ≫ ρ₂ d) → ∀ (v₁ : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₁ a] ![1, -1])) (v₂ : ∀ b, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₂ b] ![1, -1])), (∀ a, (v₁ a).IsGen) → (∀ b, (v₂ b).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (v₁ (a * c)) (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₁ c) (ρ₁ a)))) → (∀ b d, LB.Gen.Corr L _ _ _ _ (v₂ (b * d)) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₂ d) (ρ₂ b)))) → (∀ a b, LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₂ b) (ρ₁ a))) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₁ a) (ρ₂ b)))) → ∃ u : ∀ p : Ga × Gb, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), (∀ p, (u p).IsGen) ∧ ∀ p q, LB.Gen.Corr L _ _ _ _ (u (p * q)) (LB.mulGen L _ _ _ _ (u p) (LB.pullGen L _ _ (u q) (ρ p))) := by
  first | exact @GlobalTheory.ProdLin.exists_linearisation_prod | exact GlobalTheory.ProdLin.exists_linearisation_prod | (intros; apply GlobalTheory.ProdLin.exists_linearisation_prod <;> assumption)
