module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum


theorem _root_.GlobalTheory.T.lattice_class_sums_of_terms_prescribed_norms : ∀ (p : ℕ) [Fact p.Prime] (Y K : Type) [AddCommGroup Y] [Nonempty K] (m : ℕ) (q : Y → ℝ) (s : PadicAlgCl p) (n : Y → ℕ), Filter.Tendsto q Filter.cofinite Filter.atTop → (∀ χ, ‖s‖ ^ n χ = Real.exp (-q χ)) → ∀ F : Y → K → PadicAlgCl p, (∀ ν ν' κ, CongMod m ν ν' → F ν κ = F ν' κ) → (∀ ν κ, (∀ χ, CongMod m χ ν → q ν ≤ q χ) → ‖F ν κ‖ ≤ Real.exp (-q ν)) → (∀ ν, (∀ χ, CongMod m χ ν → χ ≠ ν → q ν < q χ) → ∃ κ, ‖F ν κ‖ = Real.exp (-q ν)) → ∃ t : Y → K → PadicAlgCl p, (∀ χ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧ (∀ χ, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧ ∀ ν κ (δ : ℝ), 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ χ ∈ S, CongMod m χ ν) → (∀ χ ∈ S₀, CongMod m χ ν → χ ∈ S) → ‖F ν κ - ∑ χ ∈ S, t χ κ‖ ≤ δ := by
  first | exact @GlobalTheory.UPoinc.USum.classSum_of_terms | exact GlobalTheory.UPoinc.USum.classSum_of_terms | (intros; apply GlobalTheory.UPoinc.USum.classSum_of_terms <;> assumption)
