module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesDeformationOfBoundedLatticeSeries
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.powerSeriesDeformation_of_boundedLatticeSeries : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  first | exact @GlobalTheory.MBLow.deform_of_lattice_series | exact GlobalTheory.MBLow.deform_of_lattice_series | (intros; apply GlobalTheory.MBLow.deform_of_lattice_series <;> assumption)
