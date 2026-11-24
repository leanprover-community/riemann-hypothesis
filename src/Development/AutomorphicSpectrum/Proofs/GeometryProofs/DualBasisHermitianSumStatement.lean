module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualBasisHermitianSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.dual_basis_hermitian_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component | exact GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component <;> assumption)
