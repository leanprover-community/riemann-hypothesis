module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AvgDerFamGrowth
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.avg_derFam_growth_alt : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) g‖ ≤ C * (1 + hs g) ^ N) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      MeasureTheory.AEStronglyMeasurable (fun k : ↥(Formalism.REAL.KG ε) =>
        F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) (z * Formalism.REAL.toMK k)) (Formalism.REAL.muK ε)) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    GlobalTheory.TypeSum.IsDerFam ε (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
    GlobalTheory.TypeSum.FamGrowth ε N (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  first | exact @GlobalTheory.KAvgDeriv.avg_derFam_growth | exact GlobalTheory.KAvgDeriv.avg_derFam_growth | (intros; apply GlobalTheory.KAvgDeriv.avg_derFam_growth <;> assumption)
