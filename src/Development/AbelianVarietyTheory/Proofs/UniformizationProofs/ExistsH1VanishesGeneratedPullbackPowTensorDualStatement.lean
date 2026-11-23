module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsH1VanishesGeneratedPullbackPowTensorDual
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

theorem _root_.GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (W X : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of S)) (H : LB X) (a b : W ⟶ X) (n : ℕ) (s : Fin (n + 1) → LB.Sec (H.pull a)), H.IsLB → VeryAmpleBy f (H.pull a) s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → (∀ (W₁ : Scheme.{0}) (σ : W ⟶ W₁) (a₁ b₁ : W₁ ⟶ X), σ ≫ a₁ = a → σ ≫ b₁ = b → FirstCohomologyVanishes ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ)) ∧ ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1])), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.TwistPair.twist_pair | exact GlobalTheory.TwistPair.twist_pair | (intros; apply GlobalTheory.TwistPair.twist_pair <;> assumption)
