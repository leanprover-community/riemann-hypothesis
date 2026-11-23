module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodOverRingRestrictFamilyClass
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

theorem _root_.GlobalTheory.T.period_over_ring_restrict_family_class : ∀ {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)) (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C), (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) → (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) → (∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) → ∀ {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀} {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : GlobalTheory.AnPer.Real K s σ) (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀), (∀ b, θ (σ b) = io (j b)) → (∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), r.coef.pull1 c = K.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) := by
  exact @GlobalTheory.AnPer.period_restrict_family
