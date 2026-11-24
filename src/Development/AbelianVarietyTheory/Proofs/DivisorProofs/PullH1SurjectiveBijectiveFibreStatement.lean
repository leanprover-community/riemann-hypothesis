module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibre
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.pull_h1_surjective_bijective_fibre : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | exact GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_bijective <;> assumption)
