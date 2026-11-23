module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTaylorShift
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

theorem _root_.GlobalTheory.T.close_taylor_shift_alt : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  exact @GlobalTheory.AnPer.close_taylor_shift
