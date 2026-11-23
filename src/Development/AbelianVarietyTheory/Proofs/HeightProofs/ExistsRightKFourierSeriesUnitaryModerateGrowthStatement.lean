module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowth
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_rightKFourierSeries_unitary_moderateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  first | exact @GlobalTheory.KFourier.exists_rightKFourier | exact GlobalTheory.KFourier.exists_rightKFourier | (intros; apply GlobalTheory.KFourier.exists_rightKFourier <;> assumption)
