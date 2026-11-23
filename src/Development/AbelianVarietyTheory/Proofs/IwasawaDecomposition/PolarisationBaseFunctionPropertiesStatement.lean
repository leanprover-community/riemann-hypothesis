module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.polarisationBaseFunction_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (t • B) = t * evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B) ∧ (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ B' ∈ psdCone (bar := H.bar) (X := X), evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B + evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B' ≤ evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (B + B')) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β = n) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β) := by
  first | exact @GlobalTheory.PolFan.baseFun_props | exact GlobalTheory.PolFan.baseFun_props | (intros; apply GlobalTheory.PolFan.baseFun_props <;> assumption)
