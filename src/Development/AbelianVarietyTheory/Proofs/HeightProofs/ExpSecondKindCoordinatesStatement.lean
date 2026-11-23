module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpSecondKindCoordinates
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


theorem _root_.GlobalTheory.T.exp_second_kind_coordinates : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    LinearIndependent ℝ b → (∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) →
    ∀ c : Fin d → ℝ, ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod := by
  first | exact @GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero | exact GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero | (intros; apply GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero <;> assumption)
