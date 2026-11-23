module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConstExt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.coefD_pull1_eq_perClD_of_pull1_eq_perCl : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  exact @GlobalTheory.AnPer.period_const_ext
